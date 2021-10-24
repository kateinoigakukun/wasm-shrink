ALL = simple.wasm 0.wasm

all: $(ALL)
%.wasm: %.wat
	wat2wasm $< --debug-names -o $@

.PHONY: clean
clean:
	rm -rf $(ALL)
