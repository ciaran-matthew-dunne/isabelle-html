OPTION = -o quick_and_dirty

CHAPTER = Unsorted

SESSION = GZF-HOL

OUT_DIR = output/html

ML_FILES = model_closed.ML swap_transfer.ML transfer_all_method.ML translate_locale.ML

LINKING_DIR  = $(PWD)/../scripts
PARALLEL     = $(shell cat thy_files | egrep -v '^\#' | sed s/\.thy/\.html/g )
THY_FILES    = $(shell cat thy_files | egrep -v '^\#' | tr \" " ")
USR_HEAPS    = $(shell isabelle getenv ISABELLE_HEAPS | cut -f2 -d"=")
ML_ID        = $(shell isabelle getenv ML_IDENTIFIER | cut -f2 -d"=")
HEAP_LOG_DIR = $(USR_HEAPS)/$(ML_ID)/log
HTML_DIR     = $(OUT_DIR)/$(CHAPTER)/$(SESSION)
## DB           = $(HEAP_LOG_DIR)/$(SESSION).db 

.PHONY: build html tar clean

## $(DB):  thy_files $(THY_FILES) $(ML_FILES) Makefile document/root.tex \
		document/root.bib
	
build: 
	isabelle build $(OPTION) -v -c -d . $(SESSION)

$(HTML_DIR): thy_files $(THY_FILES) $(ML_FILES) $(LINKING_DIR) ROOT Makefile
	isabelle env \
		ISABELLE_BROWSER_INFO=$(OUT_DIR)\
		isabelle build $(OPTION) -d . -c -o browser_info -v $(SESSION)

html: $(HTML_DIR)

html_linked:	$(HTML_DIR)  $(LINKING_DIR)
	rm -rf html_linked
	if [ ! -d tmphtml ]; then mkdir tmphtml; else rm -rf tmphtml/html_linked; fi
	/bin/cp -fr $(HTML_DIR) tmphtml/html_linked
	sh $(LINKING_DIR)/fix_links.sh  tmphtml/html_linked
	cat $(LINKING_DIR)/links.css >> tmphtml/html_linked/isabelle.css
	cp locale_assumptions_$(SESSION).txt tmphtml/html_linked
	cd tmphtml/html_linked; \
	 	bash $(LINKING_DIR)/parsing.sh $(SESSION); \
	 	bash $(LINKING_DIR)/linking.sh $(SESSION) . . $(PARALLEL)
	rsync -ah --exclude 'sed*' tmphtml/html_linked .

$(SESSION).tar.gz:  $(HTML_DIR) Makefile ROOT README.md
	rm -rf tmptar
	mkdir tmptar
	mkdir tmptar/src
	cp README.md tmptar
	cp -r $(LINKING_DIR) tmptar/
	cp -r README.md thythh_files $(THY_FILES) $(ML_FILES)\
	 ROOT document/ tmptar/src
	cp Makefile tmptar/src/
	 ## Avoid temporary sed files from linking:
	rsync -ah --exclude 'sed*' $(HTML_DIR)/ tmptar/html
	tar --transform "s/tmptar/$(SESSION)/g" --show-transformed-names\
	 -cvzf $(SESSION).tar.gz tmptar
	rm -rf tmptar

tar:    $(SESSION).tar.gz

clean:
	rm -rf output/ tmptar
