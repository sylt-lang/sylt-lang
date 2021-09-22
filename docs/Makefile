BUILD := build
FILES := $(wildcard *.adoc)
TARGETS := $(patsubst %.adoc,$(BUILD)/%.html,$(FILES))

.PHONY: all clean

all: $(TARGETS)

$(BUILD)/%.html: %.adoc | $(BUILD)
	asciidoctor --out-file $@ $<

$(BUILD):
	mkdir -p $@

clean:
	rm -rf $(BUILD)
