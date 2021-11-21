run: main.lua
	love .

main.lua: main.sy *.sy | sylt
	../target/debug/sylt -c $@ $<

sylt:
	cd .. && cargo b

clean:
	rm -rf main.lua

