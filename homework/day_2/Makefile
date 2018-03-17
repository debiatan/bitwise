CC = clang
WARNING_FLAGS = -W -Wall -Werror -Wno-unused-parameter -Wno-unused-variable -Wno-unused-function -Wno-write-strings -Wno-missing-field-initializers -Wno-missing-braces -Wno-format-security
CFLAGS = -O0 -g -std=c99 -MMD $(WARNING_FLAGS) -fno-strict-aliasing
# -fsanitize=undefined to check for undefined behavior at runtime

LIBS = -lm

RUNNING_INSTANCE_PID := $(shell pidof main)

all: main

-include main.d

main: main.c
	$(CC) $(CFLAGS) $(DEFINES) main.c -o $@ $(LIBS)

clean:
	$(RM) -f *.o *.d main 

