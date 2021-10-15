BUILD := build
FILES := $(wildcard *.adoc)
STYLESHEET := stylesheet.css
TARGETS := $(patsubst %.adoc,$(BUILD)/%.html,$(FILES)) $(BUILD)/sylt.png
SYNTAX := ./syntax-highlighter.rb

.PHONY: all clean

all: $(TARGETS)

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
	;

$(BUILD)/sylt.png: | $(BUILD)
	cp ../res/sylt.png $@

$(BUILD):
	mkdir -p $@

clean:
	rm -rf $(BUILD)
