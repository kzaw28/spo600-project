# Makefile for clone tests, based on volume scaling demo
# Chris Tyler 2017.11.29-2024.11.19 - Licensed under GPLv3.
# For the Seneca College SPO600 Course

# Set DUMP_ALL to a non-empty value to enable all GCC dumps
#DUMP_ALL = 1

AARCH64_BINARIES=clone-test-aarch64-prune clone-test-aarch64-noprune
X86_BINARIES=clone-test-x86-prune clone-test-x86-noprune
ifeq ($(shell echo | gcc -E -dM - | grep -c aarch64),1)
        BINARIES:=${AARCH64_BINARIES}
else
        BINARIES:=${X86_BINARIES}
endif

LIBRARIES = vol_createsample.o
CFLAGS = -g -O3 -fno-lto  -ftree-vectorize
ifdef DUMP_ALL
  CFLAGS += -fdump-tree-all -fdump-ipa-all -fdump-rtl-all
endif

all:    ${BINARIES}

clone-test-x86-prune:   clone-test-core.c ${LIBRARIES}
        gcc -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","popcnt") ))'\
                -march=x86-64 ${CFLAGS} \
                clone-test-core.c ${LIBRARIES} -o clone-test-x86-prune

clone-test-x86-noprune: clone-test-core.c ${LIBRARIES}
        gcc -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","arch=x86-64-v3") ))' \
                -march=x86-64 ${CFLAGS} \
                clone-test-core.c ${LIBRARIES} -o clone-test-x86-noprune

clone-test-aarch64-prune:       clone-test-core.c ${LIBRARIES}
        gcc -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","rng") ))'\
                -march=armv8-a ${CFLAGS} \
                clone-test-core.c ${LIBRARIES} -o clone-test-aarch64-prune

clone-test-aarch64-noprune:     clone-test-core.c ${LIBRARIES}
        gcc -D 'CLONE_ATTRIBUTE=__attribute__((target_clones("default","sve2") ))' \
                -march=armv8-a ${CFLAGS} \
                clone-test-core.c ${LIBRARIES} -o clone-test-aarch64-noprune

vol_createsample.o:     vol_createsample.c
        gcc -c ${CCOPTS} vol_createsample.c -o vol_createsample.o

clean:
        rm ${AARCH64_BINARIES} ${X86_BINARIES} || true
        rm ${LIBRARIES} || true
        rm *.c.* || true        # Should remove compiler dumpfiles