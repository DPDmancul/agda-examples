SRC := $(CURDIR)/src
MAIN := $(SRC)/index.agda
OUT := $(CURDIR)/html

.PHONY: all test html
all: html

test:
	cd "$(SRC)"; agda "$(MAIN)"

html:
	cd "$(SRC)"; agda --html --html-highlight=auto --html-dir="$(OUT)" "$(MAIN)"

.PHONY: clean
clean:
	rm -rf "$(OUT)"

.PHONY: edit
edit:
	nix-shell emacs.nix --run emacs

