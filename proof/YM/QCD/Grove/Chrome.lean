import YM.QCD.Grove.Rife
import YM.QCD.Fold.Ice
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Grove
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type*}[Fintype I][Fintype J]{c f:Side}{N n:ℕ}
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
lemma scroll (M:Matrix (Modes c N) (Modes c N) ℂ)(X:Alg (Keys c N))(h:∀ i j,M i j≠0→i.1.1=j.1.1)(v:Site c): poker locationP v (disguise M X)=disguise M (poker locationP v X):=by
    unfold disguise adapter; apply waive _ _ _ _ _ _ (Cove.boarded X); rintro (i|i) hi (j|j) he <;> try exact (he rfl).elim
    · have ht := h i j (show M i j≠0 from he); change i.1.1=v ↔ j.1.1=v; rw [ht]
    have ht := h i j (fun h=> he ((congr_arg star (show M i j=0 from h)).trans (star_zero _))); change i.1.1=v ↔ j.1.1=v; rw [ht]
lemma uphill (S:Site c→Lat.Bundle)(x:Site c)(V: Alg (Keys c N)): let Y:= disguise (copies N (Lat.rides (Equiv.refl _) S)); poker locationP x (Y V)=Y (poker locationP x V):=by
    apply scroll; rintro ⟨⟨a,b⟩,i⟩ ⟨⟨c,d⟩,j⟩ h; rw [copies,Matrix.blockDiagonal_apply] at h; split at h
    next h'=> by_contra hv; rw [rr,Equiv.refl_apply,if_neg hv] at h; exact h rfl
    next h'=> exact (h rfl).elim
local notation "C"=>EvenA c N
lemma sought (z:Frame c)(X:C)(p:Site c) : sways (Lat.rotates N z) (buds p N X)=buds p N (sways (Lat.rotates N z) X):=Subtype.ext ((uphill (fun i=>Lat.touch (colour (z i))) p X.val).symm)
lemma joyous (X:C)(p:Site c): Regal c N (buds p N X)=buds p N (Regal c N X):=by
    apply Subtype.ext; change disguise (idol c N) (changeVars (Sway.tide (Modes c N)) (cc (poker locationP p X.val)))=_ -- name
    rw [salute]
    let K:= Sway.tide (Modes c N)
    have h: poker locationP p (changeVars K (cc X.val))=changeVars K (poker locationP p (cc X.val)):=by
        apply waive _ _ _ _ _ _ (boarded _); rintro (i|i) hi (j|j) he <;> try exact (he rfl).elim
        · have ht:i=j:=by unfold K Sway.tide at he; simp [Matrix.one_apply] at he; exact he
          exact ht ▸ Iff.rfl -- motive
        have ht:i=j:=by unfold K Sway.tide at he; simp [Matrix.one_apply] at he; exact he
        exact ht ▸ Iff.rfl
    rw [← h]; exact (uphill (fun _=>wave g5) p (surf _ X.val)).symm
lemma galaxy (p:Site c)(x:C)(hx: Fit x):Fit (buds p N x):=by
    intro W h; let M:= flute (Lat.Row c) W; have hp:sways M (buds p N x)=buds p N (sways M x):=by
       apply Subtype.ext; symm; apply scroll M x.val; intro i j H; by_contra ht; have hx:i.1≠j.1:=fun h'=>ht (Prod.ext_iff.mp h').1; unfold M flute at H; simp [hx,Matrix.one_apply] at H
    exact hp.trans (congr_arg _ (hx W h)) -- supply
section periods
variable {c C' f F:Side}{D w:ℕ}{H:C'.val=c.val*D}{Z:ℕ}(A:Window c C' Z)(Y:Site C'→ℂ)
def divert (G:Matrix (Modes C' N) (Modes c N) ℂ): EvenA C' N→ₐ[ℝ] EvenA c N:= AlgHom.restrictScalars ℝ (car (adapter G Gᴴᵀ) (fun x h=>(exterior_parity _ x).trans (congr_arg _ h)))
-- unique spelling.equate
lemma pulsesG (X:Support C')(v:EvenA C' N)(hv:Gated X v) (p:Site C')(hp:p∈ X)(ha:Set.InjOn A.cut X): buds (A.cut p) N (axes A Y N v)= axes A Y N (buds p N v):=by
    let U:=choir N (stream A Y)
    have hq (i: Modes C' N)(j:Modes c N)(h:U i j≠0): A.cut i.1.1=j.1.1:=by
       unfold U choir at h; rw [Matrix.blockDiagonal_apply] at h; split at h
       next he=> unfold Quarry.stream at h; simp at h; exact congr_arg Prod.fst h.1 -- check
       next he=> exact (h rfl).elim
    apply Subtype.ext; apply waive _ _ _ _ _ v.val hv; rintro (i|i) hi (j|j) he <;> try exact (he rfl).elim
    · change i.1.1=p ↔ j.1.1=A.cut p; rw [← hq _ _ (show U i j≠0 from he)]; exact ⟨fun hz=>congr_arg _ hz,fun h=>ha ((mem_filter.mp hi).2) hp h⟩
    change i.1.1=p ↔ j.1.1=A.cut p; rw [← hq _ _ (fun h=> he (show star (U i j)=0 from (congr_arg star h).trans (star_zero _)))]; exact ⟨fun hz=>congr_arg _ hz,fun h=>ha ((mem_filter.mp hi).2) hp h⟩
lemma mud_ax (x:EvenA C' N):mud (axes A Y N x)=mud x:=by
   let U:= choir N (stream A Y); let f:= adapter U Uᴴᵀ; change coef ∅ (f x.val)=coef ∅ _; generalize hx:x.val=v; rw [← write v, map_sum,map_sum,map_sum]; refine sum_congr rfl fun i _=>?_ ; by_cases h:i=∅; · rw [h,mono_empty,map_smul,map_one,map_smul,map_smul,← mono_empty, ← mono_empty,Grass.read,Grass.read]
   have ht:(∅:Finset (Keys c N)).card≠ i.card:=fun he=> h (card_eq_zero.mp (he.symm.trans card_empty))
   rw [map_smul,map_smul,show coef ∅ (f (mono i))=0 from spectrum (Grass.exterior_layer _ (homogeneous i)) _ ht, map_smul,read_other _ _ (Ne.symm h)] -- check instances
end periods
end YM.QCD.Grove
