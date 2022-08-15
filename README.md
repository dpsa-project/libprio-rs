# Fixed point vector sum with bounded norm for libprio-rs
A fork of [libprio-rs](https://github.com/divviup/libprio-rs) aiming to enable summing vectors containing [fixed point numbers](https://en.wikipedia.org/wiki/Fixed-point_arithmetic) in a distributed private fashion, as well as verifying that the [L2 norm](https://en.wikipedia.org/wiki/Norm_(mathematics)#Euclidean_norm) of each input vector is bounded by 1.

We intend to use this code as a building block for [federated learning with global differential privacy](https://github.com/dpsa-project/overview).

We use the [fixed crate](https://docs.rs/fixed/latest/fixed/) for fixed point encoding.
