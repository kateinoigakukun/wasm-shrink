ALL = simple.wasm

all: $(ALL)
%.wasm: %.wat
	wat2wasm $< --debug-names -o $@

.PHONY: clean
clean:
	rm -rf $(ALL)
