# the compiler: gcc for C program, define as g++ for C++

CC = gcc
CFLAGS  = -O3

binaries = discharge reduce

$(TARGET): $(TARGET).c
	$(CC) $(CFLAGS) -o $(TARGET) $(TARGET).c

all: $(binaries)

.PHONY: clean

clean:
	rm -f $(binaries)
