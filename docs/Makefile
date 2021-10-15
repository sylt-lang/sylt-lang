BUILD := build
FILES := $(wildcard *.adoc)
STYLESHEET := stylesheet.css
TARGETS_HTML := $(patsubst %.adoc,$(BUILD)/%.html,$(FILES)) $(BUILD)/sylt.png
TARGETS_PDF := $(patsubst %.adoc,$(BUILD)/%.pdf,$(FILES))
SYNTAX := ./syntax-highlighter.rb

.PHONY: clean html pdf

all:
html: $(TARGETS_HTML)
pdf: $(BUILD)/sylt.pdf

$(BUILD)/%.html: %.adoc $(STYLESHEET) $(SYNTAX) | $(BUILD)
	@echo Building $@
	@asciidoctor \
		--out-file $@ $< \
		--require $(SYNTAX) \
		--attribute icons=font \
		--attribute favicon=sylt.png \
		--attribute source-highlighter=rouge \
		--attribute stylesheet=$(STYLESHEET) \
		--attribute rouge-style=base16.dark \
		--attribute toc=left \
		--attribute sectlinks \
		--attribute setanchors \
		--attribute hide-uri-scheme \
	;

$(BUILD)/sylt.pdf: $(TARGETS_PDF) | $(BUILD)
	@echo Merging into $@
	@pdfunite $^ $@ 2>/dev/null

$(BUILD)/%.pdf: %.adoc $(SYNTAX) | $(BUILD)
	@echo Building $@
	@asciidoctor-pdf \
		--out-file $@ $< \
		--require $(SYNTAX) \
		--attribute source-highlighter=rouge \
		--attribute rouge-style=github \
	;
		

$(BUILD)/sylt.png: | $(BUILD)
	cp ../res/sylt.png $@

$(BUILD):
	mkdir -p $@

clean:
	rm -rf $(BUILD)
