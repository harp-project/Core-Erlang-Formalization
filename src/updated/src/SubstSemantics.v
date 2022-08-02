Require Export Frames.

Reserved Notation "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" (at level 50).

Inductive step : FrameStack -> Exp -> FrameStack -> Exp -> Prop :=
(**  Reduction rules *)
| red_app_start v hd tl xs (H : VALCLOSED v):
  ⟨ (FApp1 (hd::tl))::xs, v ⟩ --> ⟨ (FApp2 v tl [])::xs, hd⟩
  
where "⟨ fs , e ⟩ --> ⟨ fs' , e' ⟩" := (step fs e fs' e').
