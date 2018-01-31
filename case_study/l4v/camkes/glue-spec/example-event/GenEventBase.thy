(*
 * Copyright 2014, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the GNU General Public License version 2. Note that NO WARRANTY is provided.
 * See "LICENSE_GPLv2.txt" for details.
 *
 * @TAG(NICTA_GPL)
 *)
chapter {* \label{s:eventbase}Example -- Events *}
(*<*)
(* THIS FILE IS AUTOMATICALLY GENERATED. YOUR EDITS WILL BE OVERWRITTEN. *)
theory GenEventBase
imports "../Types" "../Abbreviations" "../Connector"
begin
(*>*)

text {*
  This section provides an example following on from \autoref{h:procbase} that
  gives an example of the corresponding definitions that are generated for a
  system involving \camkes events. A system defined by the following
  specification will be used throughout:

  \camkeslisting{event.camkes}
*}

subsection {* \label{ssec:eventbase}Generated Base Theory *}

subsubsection {* \label{sssec:eventbasetypes}Types *}
text {*
  The data types generated for a system involving events are similar to those
  for a system involving procedures, however an additional instance is
  derived for every
  connection in the system that carries event messages. 
  This generated instance models the state of the event; 
  that is, whether it is pending or not.
*}

datatype channel
  = simpleEvent1

datatype inst
  = sink
  | source
  | simpleEvent1\<^sub>e

datatype Collector_channel
  = Collector_ev

datatype Emitter_channel
  = Emitter_ev

subsubsection {* \label{sssec:eventbaseprim}Interface Primitives *}
text {*
  For each component type with a @{term consumes} interface, two primitives are
  generated for each interface. These correspond to the wait and poll functions
  in generated glue code. As for procedures, @{term embed} functions must be
  supplied by the user to save the result of the operation into the component's
  local state.

  Event callbacks are not currently represented. These can be represented by
  hand in the intermediate user theory. We plan to extend the generator in
  future to wrap this functionality in a primitive for the user.
*}

definition
  Poll_Collector_ev :: "(Collector_channel \<Rightarrow> channel) \<Rightarrow>
    ('cs local_state \<Rightarrow> bool \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  "Poll_Collector_ev ch embed_data \<equiv> EventPoll (ch Collector_ev) embed_data"

definition
  Wait_Collector_ev :: "(Collector_channel \<Rightarrow> channel) \<Rightarrow>
    ('cs local_state \<Rightarrow> bool \<Rightarrow> 'cs local_state) \<Rightarrow> (channel, 'cs) comp"
where
  "Wait_Collector_ev ch embed_data \<equiv> EventWait (ch Collector_ev) embed_data"

text {*
  For each component type with an @{term emits} interface, a single primitive is
  generated to correpond to the emit function in the glue code. The emit
  definition needs no embedding or projection functions because it is
  state-independent.
*}

definition
  Emit_Emitter_ev :: "(Emitter_channel \<Rightarrow> channel) \<Rightarrow> (channel, 'cs) comp"
where
  "Emit_Emitter_ev ch \<equiv> EventEmit (ch Emitter_ev)"

subsubsection {* \label{sssec:eventbaseinst}Instantiations of Primitives *}
text {*
  As for procedure interfaces, the event primitives are specialised for each
  interface in the system by partially applying them with a function mapping
  the interface to the relevant -- in this case the only -- system connection.
*}

definition
  Poll_sink_ev :: "('cs local_state \<Rightarrow> bool \<Rightarrow> 'cs local_state) \<Rightarrow>
    (channel, 'cs) comp"
where
  "Poll_sink_ev \<equiv>
    Poll_Collector_ev (\<lambda>c. case c of Collector_ev \<Rightarrow> simpleEvent1)"

definition
  Wait_sink_ev :: "('cs local_state \<Rightarrow> bool \<Rightarrow> 'cs local_state) \<Rightarrow>
    (channel, 'cs) comp"
where
  "Wait_sink_ev \<equiv>
    Wait_Collector_ev (\<lambda>c. case c of Collector_ev \<Rightarrow> simpleEvent1)"

definition
  Emit_source_ev :: "(channel, 'cs) comp"
where
  "Emit_source_ev \<equiv>
    Emit_Emitter_ev (\<lambda>c. case c of Emitter_ev \<Rightarrow> simpleEvent1)"

(*<*)
end
(*>*)