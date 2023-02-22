SpeX_archive = SpeX.tar
pkgdata_DATA = $(SpeX_archive)
CLEANFILES = $(SpeX_archive)

SpeX_data = CommonLibs \
	Lang \
	REPL \
	SAP \
	Core.maude \
	Database.maude \
	Formatting.maude \
	Knowledge-base.maude \
	Language.maude \
	Processor.maude \
	citp.maude \
	run-citp.maude \
	quit.maude
EXTRA_DIST = $(SpeX_data)

$(SpeX_archive): $(SpeX_data)
	tar -cf $(SpeX_archive) -C $(srcdir) $(SpeX_data)

install-data-hook:
	cd $(pkgdatadir); \
	tar -vxf $(SpeX_archive) > install.manifest; \
	cat install.manifest | sed -e 's/^\|$$/"/g' | xargs chmod a=rX,u+w; \
	rm -f $(SpeX_archive)

uninstall-local:
	cd $(pkgdatadir); \
	tac install.manifest | sed -e 's/ /\\ /g' | xargs rm -fd; \
	rm -f install.manifest
