module WellFoundedLemmas 

import public Prelude.WellFounded

%access public export
%default total

getAccess : {rel : a -> a -> Type} -> 
            (x : a) -> Accessible rel x -> 
            (y : a) -> rel y x -> Accessible rel y
getAccess {rel} x (Access acc) y lt = acc y lt

accRecSpec : {rel : a -> a -> Type} ->
             (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) ->
             (z : a) -> (acc: Accessible rel z) ->
             accRec step z acc = step z (\ y, lt => accRec step y (getAccess z acc y lt))
accRecSpec step z (Access acc) = Refl

interface ExtensionalStepEq (rel : a -> a -> Type)
                            (step : (x : a) -> ((y : a) -> rel y x -> b) -> b) where
  extStepEq : (x : a) ->
              (f, g : (y : a) -> rel y x -> b) ->
              (extEq : (y : a) -> (lt : rel y x) -> f y lt = g y lt) ->
              step x f = step x g

accRecProofInvariant : (ExtensionalStepEq rel step) =>
                       (x : a) -> (r, s : Accessible rel x) ->
                       accRec step x r = accRec step x s
accRecProofInvariant {rel} {step} x (Access acc_r) (Access acc_s) =
  extStepEq x 
    (\ y, lt => accRec step y (acc_r y lt))
    (\ y, lt => accRec step y (acc_s y lt))
    (\ y, lt => accRecProofInvariant {step = step} y (acc_r y lt) (acc_s y lt))
                      
wfRecSpec : (WellFounded rel, ExtensionalStepEq rel step) =>
            (x : a) -> wfRec step x = step x (\ y, lt => wfRec step y)
wfRecSpec {rel} {step} x with (wellFounded {rel} x)
  wfRecSpec {rel} {step} x | Access acc =
    extStepEq x
      (\ y, lt => accRec step y (acc y lt))
      (\ y, lt => accRec step y (wellFounded y))
      (\ y, lt => accRecProofInvariant {rel} {step} y (acc y lt) (wellFounded y))

