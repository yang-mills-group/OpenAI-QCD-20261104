import YM.QCD.Fold.Pace
set_option linter.unusedSectionVars false
/-! # Loom-Vacuum Constraint. Keep pin invisible under deck shifts. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Folding
open Function Lattice Wilson Lat Flume Orbit Run Fork Kit Cost Finset Relation
open PhysicalNext.Repeat.Deck Push.Local Further.PhysicalPeriodLimitF933 Macrame Shingle
open Bay Strut Sway Revolve Quarry
open scoped Classical Matrix Matrix.Norms.L2Operator BigOperators
variable {c C f F:Side}{D b B:ℕ}{G:Ratio C F}{Q:Ratio c f}{v:Strut C}{u:Strut c}
variable {I J:Type}[DecidableEq I][Fintype I][DecidableEq J][Fintype J]
namespace Collum
variable (S: Collum f F I J D){A:Therm I Q S.small}{K:Therm J G S.big}(k:Site F→ℂ){T: Land F J J}
def pin (E:Ratio c f): Strut c:=(1,0)
lemma pin_hold (U:Grid f): sky (raise Q (pin Q)) U=U:=by
   have he:Q.embed 0=0:= Q.root.map_zero
   unfold pin sky raise; dsimp only; rw [he]; funext i; simp [pull, Step.read]; rfl -- edit
lemma pin_cost :Warrant (raise Q (pin Q)) (fun _=>1) 1:=by
   have hs:Q.embed 0=0:= Q.root.map_zero
   unfold pin raise; change Warrant ((1,Q.embed 0) : Strut f) _ _; rw [hs]; refine ⟨⟨fun _=>Or.inl rfl,fun i x=>?_⟩,Swing.none⟩; simp [glint, Step.used]; rfl
lemma pin_bill (x:Site f): act (raise Q (pin Q)) x=x:=by change affine 1 (Q.embed 0) x=x; rw [← Q.root_embed,Q.root.map_zero]; simp -- dir root_embed
lemma pin_ship (K: Therm I Q S.small):K.shiftP (pin Q)=Equiv.refl _:=by
   let W:= K.shiftP (pin Q); suffices h:∀ i,W i=i from Equiv.ext h; intro i; apply W.injective; have he:= K.steps (pin Q) (pin Q); rw [show pod (pin Q) (pin Q)=pin Q from Prod.ext (mul_one _) (by simp [pin,pod])] at he; exact Eq.symm (Equiv.congr_fun he i)
lemma palm (X:Support f): raiseS Q (pin Q) X=X:=by rw [show raiseS Q (pin Q) X=X.image (act (raise Q (pin Q))) from Finset.map_eq_image ..]; ext; simp only [mem_image, pin_bill]; simp -- edit
lemma p_light (x:Site f): lightP (raise Q (pin Q)) 1 (fun _=>1) x=1:=by simp [lightP,wave]
variable (Z:S.salt (pin Q) v (fun _=>1) k A K) (hp: Warrant (raise G v) k 1)(he: Held G K K T)
include hp he Z
lemma vortex (V:Grid f)(x y:J)(U:Support F)(P:Support f)(b B:ℕ):
  floret S.T S.d (S.rim x y) b B (S.big x) (S.big y) U (T x y U) P (settled V)= floret S.T S.d (S.rim (K.shiftP v x) (K.shiftP v y)) b B (S.big (K.shiftP v x)) (S.big (K.shiftP v y)) (raiseS G v U) (T (K.shiftP v x) (K.shiftP v y) (raiseS G v U)) P (settled V):=by
    have h:= S.pence _ _ _ hp (pin_cost (Q:=Q)) Z he x y V b B U P; rwa [pin_hold,p_light,p_light, palm, star_one, one_mul,mul_one] at h

-- collapse one fibre EXACT rows or columns
variable (b B:ℕ)
lemma parsed (p:J) : S.pi (K.shiftP v p)=S.pi p:=by rw [Z.2.2.1,S.pin_ship]; rfl
lemma left_trip (p:J) (i:I) (W:Grid f)(A':Support f):
 (∑ j∈parcel S.pi i,∑ y,floret S.T S.d (S.rim p j) b B (S.big p) (S.big j) y (T p j y) A' (settled W))=
   ∑ j∈parcel S.pi i,∑ y,floret S.T S.d (S.rim (K.shiftP v p) j) b B (S.big (K.shiftP v p)) (S.big j) y (T (K.shiftP v p) j y) A' (settled W):=by
   have hx j : S.pi (K.shiftP v j)=(Equiv.refl I) (S.pi j):=parsed S _ Z hp he j
   symm; nth_rw 1 [show i=(Equiv.refl I) i from rfl]; rw [ranked hx]; apply sum_congr rfl; intro j _; rw [← Equiv.sum_comp (raiseS G v)]; refine sum_congr rfl fun m _=>?_ ; exact (vortex S k Z hp he W p j m A' b B).symm
lemma right_trip (p:J) (i:I)(W:Grid f)(A':Support f):
 (∑ j∈parcel S.pi i,∑ y,floret S.T S.d (S.rim j p) b B (S.big j) (S.big p) y (T j p y) A' (settled W))=
   ∑ j∈parcel S.pi i,∑ y,floret S.T S.d (S.rim j (K.shiftP v p)) b B (S.big j) (S.big (K.shiftP v p)) y (T j (K.shiftP v p) y) A' (settled W):=by
   have hx j : S.pi (K.shiftP v j)=(Equiv.refl I) (S.pi j):=parsed S _ Z hp he j
   symm; nth_rw 1 [show i=(Equiv.refl I) i from rfl]; rw [ranked hx]; apply sum_congr rfl; intro j _; rw [← Equiv.sum_comp (raiseS G v)]; refine sum_congr rfl fun m _=>?_ ; exact (vortex S k Z hp he W j p m A' b B).symm
end Collum
end YM.QCD.Folding
