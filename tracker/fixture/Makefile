ALL = simple.wasm

all: $(ALL)
%.wasm: %.wat
	wat2wasm $< -o $@

.PHONY: clean
clean:
	rm -rf $(ALL)
