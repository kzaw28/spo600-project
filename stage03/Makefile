# Set DUMP_ALL to a non-empty value to enable all GCC dumps
 DUMP_ALL = 1

# Use the locally built GCC
CC = $(HOME)/gcc-test-001/bin/gcc

AARCH64_BINARIES = clone-test-aarch64-prune clone-test-aarch64-noprune clone-test-aarch64-tc1-prune clone-test-aarch64-tc1-noprune
X86_BINARIES = clone-test-x86-prune clone-test-x86-noprune clone-test-x86-tc1-prune clone-test-x86-tc1-noprune

ifeq ($(shell echo | $(CC) -E -dM - | grep -c aarch64),1)
    BINARIES := $(AARCH64_BINARIES)
else
    BINARIES := $(X86_BINARIES)
endif

LIBRARIES = vol_createsample.o
CFLAGS = -g -O3 -fno-lto -ftree-vectorize
ifdef DUMP_ALL
  CFLAGS += -fdump-tree-all -fdump-ipa-all -fdump-rtl-all
endif

all: $(BINARIES)

clone-test-x86-prune: clone-test-core.c $(LIBRARIES)
	$(CC) -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","popcnt") ))' \
		-march=x86-64 $(CFLAGS) clone-test-core.c $(LIBRARIES) -o clone-test-x86-prune

clone-test-x86-noprune: clone-test-core.c $(LIBRARIES)
	$(CC) -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","arch=x86-64-v3") ))' \
		-march=x86-64 $(CFLAGS) clone-test-core.c $(LIBRARIES) -o clone-test-x86-noprune

clone-test-aarch64-prune: clone-test-core.c $(LIBRARIES)
	$(CC) -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","rng") ))' \
		-march=armv8-a $(CFLAGS) clone-test-core.c $(LIBRARIES) -o clone-test-aarch64-prune

clone-test-aarch64-noprune: clone-test-core.c $(LIBRARIES)
	$(CC) -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","sve2") ))' \
		-march=armv8-a $(CFLAGS) clone-test-core.c $(LIBRARIES) -o clone-test-aarch64-noprune

vol_createsample.o: vol_createsample.c
	$(CC) -c $(CCOPTS) vol_createsample.c -o vol_createsample.o

clean:
	rm $(AARCH64_BINARIES) $(X86_BINARIES) || true
	rm $(LIBRARIES) || true
	rm *.c.* || true

# 86 clone tests

clone-test-x86-tc1-prune: test1.c $(LIBRARIES)
	$(CC) -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","popcnt")))' \
		-march=x86-64 $(CFLAGS) test1.c $(LIBRARIES) -o $@

clone-test-x86-tc1-noprune: test1.c $(LIBRARIES)
	$(CC) -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","arch=x86-64-v3")))' \
		-march=x86-64 $(CFLAGS) test1.c $(LIBRARIES) -o $@

# Aarch64 clone tests

clone-test-aarch64-tc1-prune: test1.c $(LIBRARIES)
	$(CC) -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","rng")))' \
		-march=armv8-a $(CFLAGS) test1.c $(LIBRARIES) -o $@

clone-test-aarch64-tc1-noprune: test1.c $(LIBRARIES)
	$(CC) -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","sve2")))' \
		-march=armv8-a $(CFLAGS) test1.c $(LIBRARIES) -o $@