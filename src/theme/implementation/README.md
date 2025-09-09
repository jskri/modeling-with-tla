# Build requirements

- A compiler supporting C++20.

- CMake >= 3.5


# How to build

```bash
mkdir build
cd build
cmake ..
cmake --build .
```


# How to run

In a terminal:

```bash
./client ../initial_pack.txt tcp://127.0.0.1:12345
```

In another terminal:

```bash
./server ../initial_pack.txt ../new_packs.txt tcp://127.0.0.1:12345
```
