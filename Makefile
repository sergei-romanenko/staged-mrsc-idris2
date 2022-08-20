repl:
	rlwrap idris2 SMRSC/Main.idr

# edit-tests1:
# 	cd ./tests/smrsc/test001 && rlwrap idris2 -p smrsc Main.idr

# edit-tests2:
# 	cd ./tests/smrsc/test002 && rlwrap idris2 -p smrsc Greet.idr

clean:
	rm -f tests/*.idr~
	rm -f tests/*.ibc
	rm -rf build/
	rm -rf tests/build/

.PHONY: build
build:
	idris2 --build staged-mrsc-idris2.ipkg

# this step is covered by `make build` if have set `main` and `executable` set in the `.ipkg` file.
build-executable: build # Has a dependency on build, not sure why
	idris2 ./SMRSC/Main.idr -o staged-mrsc-idris2 # this is the name of the executable
	# it will be created in ./build/exec/

run-executable: build-executable
	./build/exec/staged-mrsc-idris2

install:
	idris2 --install staged-mrsc-idris2.ipkg

install-with-src:
	idris2 --install-with-src staged-mrsc-idris2.ipkg
	
testbin:
	@${MAKE} -C tests testbin

# run like: `make test only=test002`
test-only:
	${MAKE} -C tests only=$(only)

# only run the tests that fail during the last run
retest-only:
	${MAKE} -C tests retest

test: build testbin test-only
retest: build testbin retest-only

# time-time:
# 	time ${MAKE} test INTERACTIVE=''

# docs:
# 	idris2 --mkdoc staged-mrsc-idris2.ipkg

# docker-build:
# 	docker build . -t snazzybucket/hello-idris2

# docker-run:
# 	docker run snazzybucket/hello-idris2
