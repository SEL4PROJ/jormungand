#!/usr/bin/env python
#
# An example CGI script to export multiple hgweb repos, edit as necessary

# adjust python path if not a system-wide install:
import sys
# using the hg installation provided by the system (AK, 3.3.2010)
#sys.path.insert(0, "/home/isabelle-repository/repos/mercurial-www4/lib64/python2.5/site-packages")
#sys.path.insert(0, "/usr/lib64/python2.5/site-packages")
#sys.path.insert(0, "/home/isabelle-repository/repos/mercurial-1.3.1/lib64")
#sys.path.insert(0, "/home/isabelle-repository/repos/testtool")


# enable importing on demand to reduce startup time
from mercurial import demandimport; demandimport.enable()

# Uncomment to send python tracebacks to the browser if an error occurs:
import cgitb
cgitb.enable()

# If you'd like to serve pages with UTF-8 instead of your default
# locale charset, you can do so by uncommenting the following lines.
# Note that this will cause your .hgrc files to be interpreted in
# UTF-8 and all your repo files to be displayed using UTF-8.
#
import os
os.environ["HGENCODING"] = "UTF-8"
os.environ["HGRCPATH"] = "/home/isabelle-repository/repos/hgrc"

from mercurial.hgweb.hgwebdir_mod import hgwebdir
import mercurial.hgweb.wsgicgi as wsgicgi

# The config file looks like this.  You can have paths to individual
# repos, collections of repos in a directory tree, or both.
#
# [paths]
# virtual/path = /real/path
# virtual/path = /real/path
#
# [collections]
# /prefix/to/strip/off = /root/of/tree/full/of/repos
#
# collections example: say directory tree /foo contains repos /foo/bar,
# /foo/quux/baz.  Give this config section:
#   [collections]
#   /foo = /foo
# Then repos will list as bar and quux/baz.
#
# Alternatively you can pass a list of ('virtual/path', '/real/path') tuples
# or use a dictionary with entries like 'virtual/path': '/real/path'

application = hgwebdir('/home/isabelle-repository/repos/hgweb.config')
wsgicgi.launch(application)
