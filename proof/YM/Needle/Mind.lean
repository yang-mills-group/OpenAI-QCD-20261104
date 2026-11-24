import YM.Needle.Seat
/-! Envelope calculus. 
  Uniform prices on all fine mesh placements and lifts. Necessary for spacetime
  scaling assertions and rank certificate.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Needle
open Set Function Filter Lattice Cells Lyre Lyre.Goblet Romance QCD QCD.Lat QCD.Tide QCD.Grass Plum QCD.RP Patria Patria.Depth Patria.Hub
open Finset
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {C:Sequence} (P:Calibration C)
local notation "S"=> C.S
set_option quotPrecheck false
local notation "Rᴮ" i:arg => (C.A i).regulator
local notation "B" i:arg=> C.S.side (C.R i) (C.N i)
abbrev stalk (C:Sequence) (i:ℕ):=Cover → Insertion (C.S.side (C.R i) (C.N i)) 6
noncomputable def stemV (d:ℕ)(i:ℕ)(u:Averaging): UV.Label d →ₗ[ℂ] stalk C i :=LinearMap.pi (fun b:Cover=> (P.candidate d _ b).comp (P.mix d u i).toLinearMap)
noncomputable abbrev stem (d:ℕ)(i:ℕ):= stemV P d i none
abbrev GreenP (C:Sequence)(i j:ℕ)(X:stalk C i)(v:ℝ):Prop:=∀ h:j+1 ≤ C.N i, let g:= viewW C.S (C.R i) h; ∀ T:Tiling (C.S.side (C.R i) (C.N i)), T.side.val= ratioTo C.S (C.N i) j → T.kind=.link →∀ (s:T.Cell)(b:Cover),wrap _ b∈ T.margin s (3*g.count.val) → Gold ((C.A i).regulator) T s (X b) v
namespace GreenP
variable {i j:ℕ}{x y:stalk C i}{k c:ℝ}(hx:GreenP C i j x k) (z:ℂ)
include hx
protected lemma smul : GreenP C i j (z • x) (‖z‖*k):= fun h p s a b c d=> Gold.minted (hx h p s a b c d) z
protected lemma mono (he:k≤c):GreenP C i j x c:= fun h p s a b c d=>Gold.mono (hx h p s a b c d) he
protected lemma add (hy:GreenP C i j y c):GreenP C i j (x+y) (k+c):=fun h p s a b c d=> Gold.together (hx h p s a b c d) (hy h p s a b c d)
omit hx
protected lemma zero : GreenP C i j 0 0:=fun h p s a b c d=> Gold.nil
protected lemma sum {I:Type*}(s:Finset I)(x:I→stalk C i)(v:I→ℝ)(hp:∀ k∈s, GreenP C i j (x k) (v k)): GreenP C i j (∑ k∈s,x k) (∑ k∈s,v k):=by
   induction s using Finset.induction_on with | empty=>simp only [sum_empty]; exact GreenP.zero | insert a s ha ih=> rw [sum_insert ha,sum_insert ha]; exact GreenP.add (hp a (mem_insert_self ..)) (ih fun i h=>hp i (mem_insert_of_mem h))
variable (d:ℕ)
lemma leaf {u: UV.Label d}(h: wider C P u k j i):GreenP C i j (stem P d i u) k:=by
     intro hV g T hT ht v b hb; let X:= P.physical (d:=d) none i u b; have hY:= h hV T hT ht v b hb
     change Gold _ _ _ X _
     apply Gold.mono (coin (R:=Rᴮ i) (p:=v) (Intag.Tarot.Vista.fences T hY.1) hY.1.parity); rw [← Lyre.Goblet.sprouts _ _ _ _ (show (Rᴮ i).t=0 from rfl)]; exact hY.2
end GreenP
variable {n:ℕ}(i j:ℕ)(u:Fin n→stalk C i)(v:Fin n→ℝ)
noncomputable abbrev readS (C:Sequence)(i:ℕ) (u:Fin n→stalk C i)(x:Fin n→ Cover):= ((C.A i).regulator).average (List.ofFn fun j=> u j (x j)).prod
variable {β ν:ℝ}(hC:C.Path β ν)
local notation "K_"=> C.S.side (C.R i) (C.N i)
include hC
lemma engaged(i:ℕ):(Rᴮ i).Z≠0:=by
   have h:= hC.normalized i; have hf:= (h.normal (m:=C.N i) le_rfl).ne'; rw [h.start] at hf; change joint ⇑((Rᴮ i).density*1) ≠0; rwa [mul_one]
lemma reapS (hy:∀ k,GreenP C i j (u k) (v k))(f:Fin n→ Cover)(hF:seaM C i j f)(hg:6*n<(C.S.step j).L.val)(hk:j+1 ≤ C.N i): ‖readS C i u f‖≤ ∏ i,v i:=by
    let W:= Rᴮ i; let K:= (C.S).side (C.R i) (C.N i); let g:=viewW C.S (C.R i) hk; let g':=viewW C.S (C.R i) (show j ≤ C.N i from Nat.le_of_lt hk);
    let t:=mural g' (evenW _ _ (hC.even i) _) (0:Site K); let F:=wrap K ∘ f
    have hPos:t.side.val= (ratioTo C.S (C.N i) j):=rfl; let L:=Ratio.count g
    have hγ: n*(2*(3*L.val))<t.side.val:=by rw [hPos,step_factor hk, show n*(2*(3*L.val))= (6*n)*L.val by ring]; exact Nat.mul_lt_mul_of_pos_right hg L.pos
    obtain ⟨x,hx⟩:= t.fits_together F (3*L.val) (by positivity) hγ; let X:= t.newly x; let Y(k:Fin n):= X.which (F k); have hZ : Injective Y:= by
         intro i j he; by_contra ho; apply (not_le.mpr (hF i j ho)); let P':= (hx i).1; exact X.extent P' (show F j∈ X.chamber (Y i) from he.symm ▸ (show F j∈ X.chamber (Y j) from (hx j).1))
    exact Gold.value (T:=X) Y hZ (fun i=> u i (f i)) v (fun i=>hy i hk X hPos rfl (Y i) (f i) (hx i)) rfl rfl ((hC.normalized i).beta_pos (Nat.le_refl _) |>.le) (sideW hC i _) (engaged hC i) -- order hC
end YM.Massive.Needle
#print axioms YM.Massive.Needle.GreenP.leaf
#print axioms YM.Massive.Needle.reapS
