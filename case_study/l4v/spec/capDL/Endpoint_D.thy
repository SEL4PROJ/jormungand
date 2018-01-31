(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)

(*
 * Operations on endpoints.
 *)

theory Endpoint_D
imports Invocations_D CSpace_D Tcb_D
begin

(* Inject the reply cap into the target TCB *)
definition
  inject_reply_cap :: "cdl_object_id \<Rightarrow> cdl_object_id \<Rightarrow> unit k_monad"
where
  "inject_reply_cap src_tcb_id dst_tcb_id \<equiv> do
     set_cap (src_tcb_id,tcb_pending_op_slot) $ cdl_cap.PendingSyncRecvCap src_tcb_id True; 
     insert_cap_child (ReplyCap src_tcb_id) (src_tcb_id, tcb_replycap_slot) (dst_tcb_id, tcb_caller_slot);
     return ()
  od"

(*
 * Get the slot where we should place an incoming cap for a
 * particular thread.
 *)

definition
  get_receive_slot :: "cdl_object_id \<Rightarrow> cdl_cap_ref option k_monad"
where
  "get_receive_slot thread \<equiv>
    do
      tcb \<leftarrow> get_thread thread;
      recv_slot \<leftarrow> (case (cdl_tcb_caps tcb tcb_ipcbuffer_slot) of (Some (FrameCap _ _ rights _ _ _)) \<Rightarrow> 
        if (Read \<in> rights \<and> Write \<in> rights)
          then return (cdl_intent_recv_slot (cdl_tcb_intent tcb))
        else
          return None
      | _ \<Rightarrow> return None);
      case ( recv_slot ) of
          None \<Rightarrow>
            return None
        | Some (croot, index, depth) \<Rightarrow>
            doE
              (* Lookup the slot. *)
              cspace_root \<leftarrow> unify_failure $ lookup_cap thread croot;
              result \<leftarrow> unify_failure $ lookup_slot_for_cnode_op cspace_root index depth;

              (* Ensure nothing is already in it. *)
              cap \<leftarrow> liftE $ get_cap result;
              whenE (cap \<noteq> NullCap) throw;

              returnOk $ Some result
            odE <catch> (\<lambda>_. return None)
    od
  "

(* Get the cptr's that the given thread wishes to transfer. *)
definition
  get_send_slots :: "cdl_object_id \<Rightarrow> cdl_cptr list k_monad"
where
  "get_send_slots thread \<equiv>
    do
      tcb \<leftarrow> get_thread thread;
      return $ cdl_intent_extras (cdl_tcb_intent tcb)
    od
  "

definition
  get_ipc_buffer :: "cdl_object_id \<Rightarrow> bool \<Rightarrow> cdl_object_id option k_monad"
where
  "get_ipc_buffer oid in_receive \<equiv> do
    frame_cap \<leftarrow> get_cap (oid,tcb_ipcbuffer_slot);
    (case frame_cap of
        Types_D.FrameCap _ a rights _ _ _ \<Rightarrow> if (Write \<in> rights \<and> Read \<in> rights) \<or> (Read\<in> rights \<and> \<not> in_receive)
          then return (Some a)
          else return None
        | _ \<Rightarrow> return None)
   od"

definition 
  corrupt_ipc_buffer :: "cdl_object_id \<Rightarrow> bool \<Rightarrow> unit k_monad"
  where
  "corrupt_ipc_buffer oid in_receive \<equiv> do
    buffer \<leftarrow> get_ipc_buffer oid in_receive;
    (case buffer of
        Some a \<Rightarrow> corrupt_frame a
      | None \<Rightarrow> corrupt_tcb_intent oid)
  od"

(*
 * Transfers at most one cap in addition to a number of endpoint badges.
 * 
 * Endpoint badges are transferred if the cap to be transferred is to 
 * the endpoint used in the transfer.
 *)
fun
  transfer_caps_loop :: "cdl_object_id option \<Rightarrow> cdl_object_id \<Rightarrow> 
                         (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow> cdl_cap_ref option 
                         \<Rightarrow> unit k_monad"
where
  "transfer_caps_loop ep receiver [] dest = return ()"
| "transfer_caps_loop ep receiver ((cap,slot)#caps) dest = 
      (* Transfer badge, transfer cap, or abort early if more than 
         one cap to transfer *)   
      (if is_ep_cap cap \<and> ep = Some (cap_object cap) 
      then do
        (* transfer badge *)
        corrupt_ipc_buffer receiver True;
        (* transfer rest of badges or cap *)
        transfer_caps_loop ep receiver caps dest
      od
      else if dest \<noteq> None then doE
        (* Possibly diminish rights (if diminish flag was set on endpoint) *)
        new_cap \<leftarrow> returnOk (update_cap_rights (cap_rights cap - {Write}) cap) \<sqinter> 
                  returnOk cap;

        (* Target cap is derived. This may abort transfer early. *)
        target_cap \<leftarrow> derive_cap slot new_cap;
        whenE (target_cap = NullCap) throw;
  
        (* Copy the cap across as either a child or sibling. *)
        liftE (insert_cap_child target_cap slot (the dest)
               \<sqinter> insert_cap_sibling target_cap slot (the dest));

        (* Transfer rest of badges *)
        liftE $ transfer_caps_loop ep receiver caps None
      odE <catch> (\<lambda>_. return ())
      else 
        return ())"


(*
 * Transfer caps from src to dest.
 *
 * In theory, the source thread specifies a list of caps to send, and
 * the destination thread specifies a list of cap slots to put them in.
 *
 * In the true spirit of L4 Pistachio, what _actually_ occurs during the
 * IPC transfer is hard to determine without knowing intricate details
 * of the kernel's implementation. In particular:
 *
 *   - Caps often just won't send, but still 'burn' the receive slot
 *     (ZombieCaps, ReplyCaps, IrqControlCap);
 *
 *   - Caps may not send, but still allow later caps to
 *     use the receive slot (Unwrapped endpoints);
 *
 *   - Caps may send with the rights diminished;
 *
 *   - Cap sending may stop half way (cap lookup faults);
 *
 *   - The new cap may either be a sibling or child of source cap,
 *     depending on where in the CDT the source cap is.
 *
 *   - In reality, no more than one cap will ever be sent, because only
 *     one destination cap slot is supported elsewhere in the code.
 *
 * We remove some of the details, replacing them with nondeterminism.
 *)
definition
  transfer_caps :: "cdl_object_id option \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list \<Rightarrow> 
                    cdl_object_id \<Rightarrow> cdl_object_id \<Rightarrow> unit k_monad"
where
  "transfer_caps ep caps sender receiver \<equiv>
    do
      dest_slot \<leftarrow> get_receive_slot receiver \<sqinter> return None;
      transfer_caps_loop ep receiver caps dest_slot      
    od"

(*
 * Get the set of threads waiting to receive on the given notification.
 *)
definition
  get_waiting_ntfn_recv_threads :: "cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_object_id set"
where
  "get_waiting_ntfn_recv_threads target state \<equiv>
     {x. \<exists>a. (cdl_objects state) x = Some (Tcb a) \<and>
         (((cdl_tcb_caps a) tcb_pending_op_slot) = Some (PendingNtfnRecvCap target)) }"

(* Get the set of threads waiting to receive on the given sync endpoint. *)
definition
  get_waiting_sync_recv_threads :: "cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_object_id set"
where
  "get_waiting_sync_recv_threads target state \<equiv>
     { x. \<exists>a. (cdl_objects state) x = Some (Tcb a) \<and>
         (((cdl_tcb_caps a) tcb_pending_op_slot) = Some (PendingSyncRecvCap target False)) }"

(*
 * Get the set of threads waiting to send to the given sync endpoint.
 * Return a tuple of (thread, is_call, can_grant).
 *)
definition
  get_waiting_sync_send_threads :: "cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_object_id set"
where
  "get_waiting_sync_send_threads target state \<equiv>
     {x. \<exists> rights grant call a b. (cdl_objects state) x = Some (Tcb a) \<and>
         (((cdl_tcb_caps a) tcb_pending_op_slot) = Some (PendingSyncSendCap target b call grant rights)) }"

(*
 * Get the set of threads which are bound to the given ntfn, but are
 * also waiting on sync IPC
 *)
definition
  get_waiting_sync_bound_ntfn_threads :: "cdl_object_id \<Rightarrow> cdl_state \<Rightarrow> cdl_object_id set"
where
  "get_waiting_sync_bound_ntfn_threads ntfn_id state \<equiv>
     {x. \<exists>a ep_id. (cdl_objects state) x = Some (Tcb a) \<and>
         (((cdl_tcb_caps a) tcb_pending_op_slot) = Some (PendingSyncRecvCap ep_id False)) \<and>
         (((cdl_tcb_caps a) tcb_boundntfn_slot) = Some (BoundNotificationCap ntfn_id))}"

(*
 * Mark a thread blocked on IPC.
 *
 * Theads get a new implicit "send once" or "receive once" capability
 * when they block on an IPC. This is because if the capability they
 * used to start the send/receive is revoked, the transfer will still be
 * allowed to proceed (even if it is at a much later point in time).
 *)

definition
  block_thread_on_ipc :: "cdl_object_id \<Rightarrow> cdl_cap \<Rightarrow> unit k_monad"
where
  "block_thread_on_ipc tcb cap \<equiv> set_cap (tcb, tcb_pending_op_slot) cap" (* Might need to do some check here *)

definition
  lookup_extra_caps :: "cdl_object_id \<Rightarrow> cdl_cptr list \<Rightarrow> (cdl_cap \<times> cdl_cap_ref) list fault_monad"
where
  "lookup_extra_caps thread cptrs \<equiv>
     mapME (\<lambda>cptr. lookup_cap_and_slot thread cptr) cptrs"

(*
 * Transfer a message from "sender" to "receiver", possibly copying caps
 * over in the process. If a fault is pending in receiver, send fault instead.
 *)
definition
  do_ipc_transfer :: "cdl_object_id option \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object_id \<Rightarrow> bool \<Rightarrow> unit k_monad"
where
  "do_ipc_transfer ep_id sender_id receiver_id can_grant \<equiv> do
      (* look up cap transfer *)
      src_slots \<leftarrow> get_send_slots sender_id;
      do (* do normal transfer *)
        caps \<leftarrow> if can_grant then 
                lookup_extra_caps sender_id src_slots <catch> (\<lambda>_. return [])
              else
                return [];
        (* copy registers, transfer message or fault *)
        corrupt_ipc_buffer receiver_id True; 
        (* transfer caps if no fault occured *)
        transfer_caps ep_id caps sender_id receiver_id
      od  \<sqinter>  (* fault transfer *)
      corrupt_ipc_buffer receiver_id True;
      (* set message info *)
      corrupt_tcb_intent receiver_id
  od"


(*
 * Transfer a message from "sender" to "receiver" using a reply capability.
 *
 * A reply capability always gives the sender the right to grant caps
 * over the channel. As the original sender must have had grant rights
 * to establish the reply cap to begin with (and hence could have
 * granted the other side a return communication path), this does not
 * increase any rights.
 *
 * If a fault is pending in the receiver, the fault is transferred.
 *)

definition
  do_reply_transfer :: "cdl_object_id \<Rightarrow> cdl_object_id \<Rightarrow> cdl_cap_ref \<Rightarrow> unit k_monad"
where
  "do_reply_transfer sender_id receiver_id reply_cap_slot \<equiv>
    do
      has_fault \<leftarrow> get_thread_fault receiver_id; 
      when (\<not> has_fault) $ do_ipc_transfer None sender_id receiver_id True;
      (* Clear out any pending operation caps. *)
      delete_cap_simple reply_cap_slot;
      when (has_fault) $ (do corrupt_tcb_intent receiver_id;
        update_thread_fault receiver_id (\<lambda>_. False) od );
      if ( \<not> has_fault) then set_cap (receiver_id,tcb_pending_op_slot) RunningCap
      else 
         (set_cap (receiver_id,tcb_pending_op_slot) NullCap 
        \<sqinter> set_cap (receiver_id,tcb_pending_op_slot) RestartCap )
    od"

(* Wake-up a thread waiting on an notification. *)
definition
  do_notification_transfer :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "do_notification_transfer receiver_id \<equiv> do
      set_cap (receiver_id,tcb_pending_op_slot) RunningCap;
      corrupt_tcb_intent receiver_id
   od"

(*
 * Signal on a notification.
 *
 * If someone is blocked on the notifications, we wake them up. Otherwise,
 * this is a no-op.
 *)

definition
  send_signal_bound :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "send_signal_bound ntfn_id \<equiv> do
      bound_tcbs \<leftarrow> gets $ get_waiting_sync_bound_ntfn_threads ntfn_id;
      if (bound_tcbs \<noteq> {}) then do
          t \<leftarrow> select bound_tcbs;
          set_cap (t, tcb_pending_op_slot) NullCap;
          do_notification_transfer t
        od
      else return ()
    od"

(* FIXME names *)
definition
  send_signal :: "cdl_object_id \<Rightarrow> unit k_monad"
where
  "send_signal ep_id \<equiv>
    (do waiters \<leftarrow> gets $ get_waiting_ntfn_recv_threads ep_id;
          t \<leftarrow> option_select waiters;
          case t of
              None \<Rightarrow> return ()
            | Some receiver \<Rightarrow> do_notification_transfer receiver
     od)
            \<sqinter> send_signal_bound ep_id"

(*
 * Receive a signal (receive from a notification).
 *
 * We will either receive data or block waiting.
 *)
definition
  recv_signal :: "cdl_object_id \<Rightarrow> cdl_cap \<Rightarrow> unit k_monad"
where
  "recv_signal tcb_id_receiver ep_cap  \<equiv> do
     ep_id \<leftarrow> return $ cap_object ep_cap; 
     block_thread_on_ipc tcb_id_receiver (PendingNtfnRecvCap ep_id) \<sqinter> corrupt_tcb_intent tcb_id_receiver
   od"

(*
 * Send an IPC to the given endpoint. If someone is waiting, we wake
 * them up. Otherwise, we put the sender to sleep.
 *)
definition
  send_ipc :: "bool \<Rightarrow> bool \<Rightarrow> cdl_badge \<Rightarrow> bool \<Rightarrow> cdl_object_id \<Rightarrow> cdl_object_id \<Rightarrow> unit k_monad"
where
  "send_ipc block call badge can_grant tcb_id_sender ep_id \<equiv>
    do
      waiters \<leftarrow> gets $ get_waiting_sync_recv_threads ep_id;
      t \<leftarrow> option_select waiters;
      case t of
          None \<Rightarrow>
            if block then
              block_thread_on_ipc tcb_id_sender
                  (PendingSyncSendCap ep_id badge call can_grant False)
            else
              return ()
        | Some tcb_id_receiver \<Rightarrow> do
             do_ipc_transfer (Some ep_id) tcb_id_sender tcb_id_receiver can_grant;
             set_cap (tcb_id_receiver,tcb_pending_op_slot) RunningCap; 
             (when (can_grant) $ (inject_reply_cap tcb_id_sender tcb_id_receiver)) \<sqinter>
             set_cap (tcb_id_sender,tcb_pending_op_slot) NullCap \<sqinter> return ()
          od
    od"

(*
 * Receive an IPC from the given endpoint. If someone is waiting, we
 * wake them up. Otherwise, we put the receiver to sleep.
 *)
definition
  receive_sync :: "cdl_object_id \<Rightarrow> cdl_object_id \<Rightarrow> unit k_monad"
where
  "receive_sync thread ep_id \<equiv> do
    waiters \<leftarrow> gets $ get_waiting_sync_send_threads ep_id;
      t \<leftarrow> option_select waiters;
      (case t of
          None \<Rightarrow>
            block_thread_on_ipc thread (PendingSyncRecvCap ep_id False) \<sqinter> corrupt_tcb_intent thread
        | Some tcb_id_sender \<Rightarrow> (do
            tcb \<leftarrow> get_thread tcb_id_sender;
            case ((cdl_tcb_caps tcb) tcb_pending_op_slot) of
              Some (PendingSyncSendCap target _ call grant rights)\<Rightarrow>(do
                 do_ipc_transfer (Some ep_id) tcb_id_sender thread grant;
                 (when (grant) $ (inject_reply_cap tcb_id_sender thread)) \<sqinter> 
                 set_cap (tcb_id_sender,tcb_pending_op_slot) RunningCap \<sqinter>
                 set_cap (tcb_id_sender, tcb_pending_op_slot) NullCap
              od)

        od)
      )
    od"

(* This is more nonderministic than is really required, but
   it makes the refinement proofs much easier *)
definition
  receive_ipc :: "cdl_object_id \<Rightarrow> cdl_object_id \<Rightarrow> unit k_monad"
where
  "receive_ipc thread ep_id \<equiv> corrupt_tcb_intent thread \<sqinter> receive_sync thread ep_id"

definition
  invoke_endpoint :: "bool \<Rightarrow> bool \<Rightarrow> cdl_endpoint_invocation \<Rightarrow> unit k_monad"
where
  "invoke_endpoint is_call can_block params \<equiv> case params of
    SyncMessage badge can_grant ep_id \<Rightarrow> do
      thread \<leftarrow> gets_the cdl_current_thread;
      send_ipc can_block is_call badge can_grant thread ep_id
    od"

definition
  invoke_notification :: "cdl_notification_invocation \<Rightarrow> unit k_monad"
where
  "invoke_notification params \<equiv> case params of
    Signal badge ep_id \<Rightarrow>
      send_signal ep_id"

definition
  invoke_reply :: "cdl_reply_invocation \<Rightarrow> unit k_monad"
where
  "invoke_reply params \<equiv> case params of
    ReplyMessage recv reply_cap_ref \<Rightarrow> do
      send \<leftarrow> gets_the cdl_current_thread;
      do_reply_transfer send recv reply_cap_ref
    od"


(*
 * Send a fault IPC to the given thread's fault handler.
 *)
definition
  send_fault_ipc :: "cdl_object_id \<Rightarrow> unit fault_monad"
  where
  "send_fault_ipc tcb_id \<equiv>
    doE
      (* Lookup where we should send the fault IPC to. *)
      tcb \<leftarrow> liftE $ get_thread tcb_id;
      target_ep_cptr \<leftarrow> returnOk $ cdl_tcb_fault_endpoint tcb;
      handler_cap \<leftarrow> lookup_cap tcb_id target_ep_cptr;
      (case handler_cap of
          EndpointCap ref badge rights \<Rightarrow>
            if Write \<in> rights \<and> Grant \<in> rights then
              liftE $ do 
                update_thread_fault tcb_id (\<lambda>_. True);
                send_ipc True False badge True tcb_id ref
              od
            else
               throw
        | _ \<Rightarrow> throw)
    odE"

(*
 * Handle a fault caused by the current thread.
 *
 * The abstract spec adds two additional parameters:
 *
 *    1. The fault type (which we abstract away);
 *
 *    2. The thread causing the fault (which always turns out
 *       to be the current thread).
 *)
definition
  handle_fault :: "unit k_monad"
where
  "handle_fault \<equiv> do
    tcb_id \<leftarrow> gets_the cdl_current_thread;
    (send_fault_ipc tcb_id
      <catch> (\<lambda>_. KHeap_D.set_cap (tcb_id,tcb_pending_op_slot) cdl_cap.NullCap))
  od"

end
