main.lua: main.sy *.sy | sylt
	../target/debug/sylt -c $@ $<

run: main.lua
	love .

sylt:
	cd .. && cargo b


