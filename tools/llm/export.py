#!/usr/bin/env python3
"""Convert a llama2.c checkpoint to safetensors (ADR 0067, section 2).

The input is the legacy `.bin` format that llama2.c's `run.c` reads, as
published for karpathy/tinyllamas (`stories260K.bin`, `stories15M.bin`): a
header of seven little-endian int32s (dim, hidden_dim, n_layers, n_heads,
n_kv_heads, vocab_size, seq_len), then the weights as f32 in `run.c`'s
order. A negative vocab_size means the classifier is not shared with the
token embedding and follows the weights.

The output names each tensor as llama2.c's `model.py` does
(`tok_embeddings.weight`, `layers.0.attention.wq.weight`, ...), with
PyTorch's (out, in) shapes, and writes the config to `__metadata__` as
strings. The members of the JSON header are in the order of their data, so
each tensor's bytes start where the previous one's end: the layout the
safetensors library writes, and the one `Pia.Format.Safetensors` reads.
The header is padded with spaces to a multiple of 8 bytes.

The f32 bytes are copied as they are, so only the standard library is
needed. The script is not part of the build or the trusted base.

    python3 tools/llm/export.py stories260K.bin stories260K.safetensors
"""

import argparse
import json
import struct
import sys

CONFIG_FIELDS = (
    "dim",
    "hidden_dim",
    "n_layers",
    "n_heads",
    "n_kv_heads",
    "vocab_size",
    "seq_len",
)


def read_config(raw):
    """The seven header fields, and whether the classifier is shared."""
    if len(raw) < 28:
        raise ValueError("shorter than the 28-byte config header")
    values = dict(zip(CONFIG_FIELDS, struct.unpack("<7i", raw[:28])))
    shared = values["vocab_size"] > 0
    values["vocab_size"] = abs(values["vocab_size"])
    for name, value in values.items():
        if value <= 0:
            raise ValueError(f"config field {name} is {value}")
    if values["dim"] % values["n_heads"] != 0:
        raise ValueError("dim is not a multiple of n_heads")
    if values["n_heads"] % values["n_kv_heads"] != 0:
        raise ValueError("n_heads is not a multiple of n_kv_heads")
    return values, shared


def layout(cfg, shared):
    """The tensors in file order: (name, shape), with a skip of `None` for
    the RoPE tables run.c no longer reads."""
    dim = cfg["dim"]
    hidden = cfg["hidden_dim"]
    layers = cfg["n_layers"]
    head = dim // cfg["n_heads"]
    kv = cfg["n_kv_heads"] * head

    # run.c stores each kind of weight for all layers together, so the
    # file order is by kind, then by layer.
    def per_layer(fmt, shape):
        return [(fmt.format(i), shape) for i in range(layers)]

    order = [("tok_embeddings.weight", (cfg["vocab_size"], dim))]
    order += per_layer("layers.{}.attention_norm.weight", (dim,))
    order += per_layer("layers.{}.attention.wq.weight", (dim, dim))
    order += per_layer("layers.{}.attention.wk.weight", (kv, dim))
    order += per_layer("layers.{}.attention.wv.weight", (kv, dim))
    order += per_layer("layers.{}.attention.wo.weight", (dim, dim))
    order += per_layer("layers.{}.ffn_norm.weight", (dim,))
    order += per_layer("layers.{}.feed_forward.w1.weight", (hidden, dim))
    order += per_layer("layers.{}.feed_forward.w2.weight", (dim, hidden))
    order += per_layer("layers.{}.feed_forward.w3.weight", (hidden, dim))
    order.append(("norm.weight", (dim,)))
    # freq_cis_real and freq_cis_imag, seq_len * head / 2 floats each.
    order.append((None, (2 * (cfg["seq_len"] * head // 2),)))
    if not shared:
        order.append(("output.weight", (cfg["vocab_size"], dim)))
    return order


def elements(shape):
    n = 1
    for d in shape:
        n *= d
    return n


def convert(raw):
    """The safetensors bytes for the checkpoint `raw`."""
    cfg, shared = read_config(raw)
    pos = 28
    tensors = []
    for name, shape in layout(cfg, shared):
        size = 4 * elements(shape)
        if pos + size > len(raw):
            raise ValueError(f"the file ends inside {name or 'the RoPE tables'}")
        if name is not None:
            tensors.append((name, shape, raw[pos : pos + size]))
        pos += size
    if pos != len(raw):
        raise ValueError(f"{len(raw) - pos} bytes follow the last weight")

    meta = {k: str(v) for k, v in cfg.items()}
    meta["shared_classifier"] = "1" if shared else "0"
    meta["format"] = "llama2.c"
    header = {"__metadata__": meta}
    offset = 0
    for name, shape, data in tensors:
        header[name] = {
            "dtype": "F32",
            "shape": list(shape),
            "data_offsets": [offset, offset + len(data)],
        }
        offset += len(data)
    text = json.dumps(header, separators=(",", ":")).encode()
    text += b" " * (-len(text) % 8)
    out = [struct.pack("<Q", len(text)), text]
    out += [data for _, _, data in tensors]
    return b"".join(out)


def main():
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("checkpoint", help="a llama2.c .bin checkpoint")
    parser.add_argument("output", help="the .safetensors file to write")
    args = parser.parse_args()
    with open(args.checkpoint, "rb") as f:
        raw = f.read()
    try:
        out = convert(raw)
    except ValueError as e:
        sys.exit(f"{args.checkpoint}: {e}")
    with open(args.output, "wb") as f:
        f.write(out)


if __name__ == "__main__":
    main()
