SRC := $(CURDIR)/src
MAIN := $(SRC)/index.agda
TMP := $(CURDIR)/tmp
OUT := $(CURDIR)/book

.PHONY: all test html
all: html

test:
	cd "$(SRC)"; agda "$(MAIN)"

html: $(SRC)/index.agda 
# clean before build
	@rm -rf "$(TMP)"
	cd "$(SRC)"; agda --html --html-highlight=auto --html-dir="$(TMP)" "$(MAIN)"
# do not use agda index but md one
	@rm "$(TMP)/index.html"
	@cp "$(SRC)/"*.md "$(TMP)"
	@sed 's%(\([^)]*\)\.lagda\.md)%(\1.md)%' "$(SRC)/SUMMARY.md" > "$(TMP)/SUMMARY.md"
# agda css must have precedence
	@chmod +w "$(TMP)/"*.css
	@sed -i 's/\(;\? *}\|;\)/ !important\1/' "$(TMP)/"*.css
	mdbook build


%/index.agda: $(SRC)/SUMMARY.md
	@mkdir -p "$*"
	grep ".lagda.md)" "$<" | sed 's%^.*\](\./\([^.]*\)\.lagda.md).*$$%import \1%' >> "$@"

.PHONY: clean
clean:
	rm -rf "$(OUT)" "$(TMP)"

.PHONY: edit
edit:
	nix-shell emacs.nix --run emacs

