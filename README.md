Foundational Cryptography Framework for machine-checked proofs of cryptography in the computational model.    

# Dependencies

Coq 8.6 or 8.5

# Building

`make` 

# Exploring 

Then open a simple example from the “src/examples” directory in Proof General.  A good place to start is “ElGamal.v.”  Interactively step through this proof to learn how to develop a simple proof of non-adaptive security in the concrete setting.  PRF_Encryption_IND_CPA.v contains a more complex proof of adaptive security along with a proof in the asymptotic setting.  

`src/ESPADA` contains a proof of security of ESPADA SSE Scheme (but see below for removed files).

The publications describing FCF are available at adam.petcher.net.   

# Importing

  env COQPATH=/path/to/fcf/src proofgeneral test.v
  Require Import FCF.FCF.

# History

Files that mo longer build have been removed:

  deleted:    src/ESPADA/ESPADA_SSE_OXT.v
  deleted:    src/ESPADA/ESPADA_SSE_OXT_Games.v
  deleted:    src/ESPADA/ESPADA_SSE_SKS_Secure.v
  deleted:    src/ESPADA/ESPADA_SSE_SKS_Secure_auto.v
  deleted:    src/ESPADA/ESPADA_TSet_Correct.v
  deleted:    src/ESPADA/ESPADA_TSet_Correct_Once.v
  deleted:    src/ESPADA/ESPADA_TSet_Once.v
  deleted:    src/ESPADA/ESPADA_TSet_Secure.v
  deleted:    src/FCF/Class.v
  deleted:    src/FCF/ConstructedFunc.v
  deleted:    src/FCF/Encryption_2W.v
  deleted:    src/FCF/ExpectedPolyTime.v
  deleted:    src/FCF/ListHybrid.v
  deleted:    src/FCF/PRP_PRF.v
  deleted:    src/FCF/Procedure.v
  deleted:    src/FCF/RandPermSwitching.v
  deleted:    src/FCF/RndDup.v
  deleted:    src/FCF/Sigma.v
  deleted:    src/FCF/State.v
  deleted:    src/FCF/examples/Commit.v
  deleted:    src/FCF/examples/EC_DRBG.v

# Ackowledgements

This work is sponsored by the Department of the Air Force under Air Force Contract FA8721-05-C-0002. Opinions, interpretations, conclusions, and recommendations are those of the author and are not necessarily endorsed by the United States Government.

This work is sponsored by the Intelligence Advanced Research Projects Activity under Air Force Contract FA8721-05-C-0002. Opinions, interpretations, conclusions, and recommendations are those of the author and are not necessarily endorsed by the United States Government.
