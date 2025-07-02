# virt-model
Formalisation in Coq of an idealised virtualisation model (partial).


This project was developed in 2018 as a final project for the university course **Construcción Formal de Programas en Teoría de Tipos** (*Formal Construction of Programs in Type Theory*). The lectures were delivered by Professors Carlos Luna and Dante Zanarini.

It formalises a section of the model described in the paper:

> *Formally Verifying Isolation and Availability in an Idealized Model of Virtualization*  
> G. Barthe, G. Betarte, J. D. Campo, and C. Luna (2011)

The paper presents a comprehensive formal model of virtualisation, including various system actions and a wide range of safety properties. This project captures a **partial formalisation** of that model, focusing on:

- Representing core components of the system state  
- Defining a small set of actions (`read`, `write`, `chmod`)  
- Proving a subset of the properties related to valid states and safety

The model and proofs are written in **Coq**. This is an educational project and does not aim to fully reproduce the entire model from the paper. It serves as a minimal demonstration of formal modelling and property verification in Coq.

## Build Instructions

To compile the project:
```bash
coqc -Q src VirtModel src/State.v
coqc -Q src VirtModel src/Actions.v
```

To open the files using the CoqIDE editor:
```bash
coqide -Q src VirtModel src/State.v src/Actions.v
```
