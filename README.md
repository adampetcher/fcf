Foundational Cryptography Framework for machine-checked proofs of cryptography in the computational model.    

# Dependencies

Coq 8.8

# Building

`make` 

# Exploring 

Then open a simple example from the “src/examples” directory in Proof General.  A good place to start is “ElGamal.v.”  Interactively step through this proof to learn how to develop a simple proof of non-adaptive security in the concrete setting.  PRF_Encryption_IND_CPA.v contains a more complex proof of adaptive security along with a proof in the asymptotic setting.  


The publications describing FCF are available at adam.petcher.net.   

# Importing

  env COQPATH=/path/to/fcf/src proofgeneral test.v
  Require Import FCF.FCF.

# History

This repository used to contain a proof of security of ESPADA SSE Scheme under
`src/ESPADA`. This proof is no longer maintained; it is preserved in git
history.

Some files that no longer fully build are preserved under `src/FCF/Broken`.
There be dragons, though -- not all of them were ever finished, and some contain
significant `admit`s.

# Ackowledgements

This work is sponsored by the Department of the Air Force under Air Force Contract FA8721-05-C-0002. Opinions, interpretations, conclusions, and recommendations are those of the author and are not necessarily endorsed by the United States Government.

This work is sponsored by the Intelligence Advanced Research Projects Activity under Air Force Contract FA8721-05-C-0002. Opinions, interpretations, conclusions, and recommendations are those of the author and are not necessarily endorsed by the United States Government.
