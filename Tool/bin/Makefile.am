bin_SCRIPTS = citp
CLEANFILES = $(bin_SCRIPTS)
EXTRA_DIST = citp.in

do_subst = sed -e 's,[@]pkgdatadir[@],$(pkgdatadir),g' \
	       -e 's,[@]maude[@],$(M3),g'

citp: citp.in Makefile
	$(do_subst) < $(srcdir)/citp.in > citp
	chmod +x citp
