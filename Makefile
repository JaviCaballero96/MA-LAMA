.PHONY: all preprocess search clean

all: preprocess search

preprocess:
	$(MAKE) -C preprocess

search:
	$(MAKE) -C search

clean:
	$(MAKE) -C preprocess clean
	$(MAKE) -C search clean
