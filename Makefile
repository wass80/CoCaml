./build/Main.js: ./app/Main.hs
	hastec -v $< $(wildcard ./src/*.hs) -o $@

