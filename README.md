# How to Mingle Streams

A Rocq project exploring how to mingle streams.

## Requirements

- **Rocq:** compatible with the version specified by the project.
- **Rocq Dune integration:** 0.13.
- **Dune:** 3.23 or compatible.
- **OPAM:** for dependency and environment management.
- **VS Code:** with the VS Rocq extension installed.

Make sure your OPAM environment is initialized and the required Rocq packages are available.

## Setup

1. **Clone the repository**

   ```bash
   git clone https://github.com/WeneKouarfate/How-to-mingle-streams.git
   cd How-to-mingle-streams
   code .
    ```

2. **Install project dependencies**

    ```bash
    opam install . --deps-only
    ```

3. **Build the project**

    ```bash
    dune build
    ```

4. **Verify in VS Code**

    Open `theories/Stream.v` for the library and `Diags.v` for the paper related definitions.
