import YM.Rill.Plots
/-! Full scale itinerary. Offices and private-box batches. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Tarn.Quilt
open YM.Analysis YM.Fir Fir Fir.Gains Fir.TagF Filter Set Metric
open Lattice Cells Lyre QCD QCD.Lat QCD.Tide QCD.Grass QCD.Plum QCD.RP QCD.Revolve UV Needle Patria Patria.Depth Patria.Hub Poised Plans Plans.Stamp Intag Intag.Vale Romance
open scoped Topology ContDiff BigOperators Classical ComplexOrder
open Function Sash TorusPCAC.Geometry Finset Goblet
variable {C:Sequence} {P:Calibration C} {n:ℕ} {β e:ℝ}(hp:C.Path β e) (i j ℓ:ℕ) (h:j+1 ≤ ℓ)(hv:ℓ+1 ≤ C.N i)
variable {I J:Type}[Fintype I][Fintype J] (y:I→ Cover)(t:J→ Cover)(f:Strings n)(g:Fin n→ stalk C i)(b:Fin n→ ℝ)(k:Fin n→Bool)
-- each centre anchored at one y i up to ANY pitch displacement. small not shifted representation needed.Always count exteriors independent.
set_option quotPrecheck false
local notation "τ"=> ratioTo C.S (C.N i) j
local notation "w"=>ratioTo C.S (C.N i) ℓ
local notation "W"=>C.S.side (C.R i) (C.N i)
variable (hC:Fintype.card I*8 < (C.S.step j).L.val)(hz:Fintype.card J*6 < (C.S.step ℓ).L.val) (hK:∀ p,k p=true→∃ x:I,∃ z:Cover, f p= y x+ (ratioTo C.S (C.N i) j) • z) (hp':∀ p,k p=false→∃ x:J,f p=t x)
variable (hU:∀ p q:Fin n,p≠q→ ratioTo C.S (C.N i) ℓ < separation (wrap (C.S.side (C.R i) (C.N i)) (f p)) (wrap _ (f q))) (hQ:∀ p q: Fin n,p≠q→ k p=true→ ratioTo C.S (C.N i) j < separation (wrap (C.S.side (C.R i) (C.N i)) (f p)) (wrap _ (f q))) (hc:∀ p,k p=true→ GreenP C i j (g p) (b p)) (hu:∀ p,k p=false→ GreenP C i ℓ (g p) (b p))
include hp h hv hC hz hK hp' hU hQ hc hu
set_option maxHeartbeats 540000 in
lemma twin : ‖readS C i g f‖ ≤∏ j,b j :=by
    have he:ℓ ≤ C.N i:= Nat.le_of_lt hv; have hl:j ≤ℓ:= Nat.le_of_lt h; let τ':=viewW C.S (C.R i) (hl.trans he); let G:=viewW C.S (C.R i) he; let V:=viewW C.S (C.R i) hl; let D:=viewW C.S (C.R i) h; let d:=3*D.count.val; let e':=viewW C.S (C.R i) hv; let r:=wrap W; let A:=3*e'.count.val; have hw:0 <A:=by unfold A; positivity
    let E:=evenW C.S (C.R i) (hp.even i) j; let E':=evenW C.S (C.R i) (hp.even i) ℓ; have hG := viewOdd C.S (C.R i) he
    have hF:Fintype.card I*(2*(d+1)) < V.count.val:=by
         change Fintype.card I * (2*(d+1)) < ratioTo C.S ℓ j; rw [step_factor h]; refine lt_of_le_of_lt (show Fintype.card I*(2*(d+1)) ≤ (Fintype.card I *8)*D.count.val from ?_) (Nat.mul_lt_mul_of_pos_right hC D.count.pos); rw [mul_assoc]; apply Nat.mul_le_mul_left; unfold d; have h:=D.count.pos; omega
    have hZ: Fintype.card J*(2*A)<G.count.val:=by
         change Fintype.card J*(2*A)< w; rw [step_factor hv]; apply lt_of_eq_of_lt _ (Nat.mul_lt_mul_of_pos_right hz e'.count.pos); change Fintype.card J*(2*(3*e'.count.val))=(Fintype.card J*6)*e'.count.val; ring
    obtain ⟨x,h1,h2⟩:= joints τ' V G E E' (viewOdd ..) (viewOdd ..) (r∘y) (r ∘t) d A hF hZ hw
    let T:=mural τ' E x; let Wi:= mural G E' x; let K(m:Fin n):= r (f m); let v(m:Fin n):=T.which (K m); let B(m:Fin n):=Wi.which (K m)
    have hn(m:Fin n)(hh:k m=false): K m∈ Wi.margin (B m) A:=by
        obtain ⟨p,hp⟩:=hp' m hh; obtain ⟨q,hq⟩:=h2 p; have h:K m∈Wi.margin q A:=by unfold K; rw [hp]; exact hq
        rw [show B m=q from Wi.which_chamber h.1]; exact h
    have hm(m:Fin n)(hh:k m=true): K m∈ T.margin (v m) (G.count.val*d):=by
        obtain ⟨p,z,h⟩:=hK m hh; obtain ⟨q,hq⟩:= h1 p; let t:= wrap (C.S.side (C.R i) j) z; have hz: K m = r (y p) + τ'.embed t:=by unfold K r; rw [h,map_add]; exact congr_arg _ (Ratio.embed_wrap τ' z).symm
        have h':K m∈ T.margin (q+t) _:= Vent.resp τ' x t E (viewOdd ..) _ hq hz -- order fields
        rw[show v m=(q+t:Site (C.S.side (C.R i) j)) from T.which_chamber h'.1]; exact h'
    have hθ(l:Fin n):K l∈ T.chamber (v l):=by
        cases hh:k l; swap; · exact (hm l hh).1
        obtain ⟨p,hp⟩:=tucked τ' V G E E' (viewOdd ..) hG x (B l); have h:=hp (hn l hh).1; rw [show v l= _ from T.which_chamber h]; exact h
    have hy: Unity T Wi v B k:=by
        constructor
        · intro m l hh he
          apply Classical.byContradiction; intro ho
          have h: T.side.val < separation (K m) (K l):=hQ m l ho he
          exact (not_le_of_gt h) (T.extent (hθ m) (hh.symm ▸ (show K l∈ T.chamber (v l) from hθ l)))
        · intro m hh; obtain ⟨p,hp⟩:= tucked τ' V G E E' (viewOdd ..) hG x (B m); rw[show v m=p from T.which_chamber (hp (hn m hh).1)]; exact hp
        intro l t hl ht H
        apply Classical.byContradiction; intro ho
        have hθ: Wi.side.val < separation (K l) (K t):= hU l t ho
        have h0: K t ∈ Wi.chamber (B l) :=by rw [H]; exact (hn t ht).1
        exact hθ.not_ge (Wi.extent (hn l hl).1 h0)
    obtain ⟨L⟩:=Ladder.adorn V G τ' (viewOdd ..) (viewOdd ..) E E' x; let j':=viewW C.S (C.R i) (h.trans he); have hD : G.count.val*d= 3*j'.count.val:=by unfold d j'; rw [YM.Next.Rank.Station.size_comp D G]; ring
    exact package T Wi _ rfl rfl L (Ladder.fullC G hG E' x) rfl ((hp.normalized i).beta_pos (Nat.le_refl _)|>.le) (sideW hp i _) (engaged hp i) (fun p=> g p (f p)) b v B k hy (fun p=>by
          unfold flight; split; next H=> exact hc p H (h.trans he) T rfl rfl _ _ (hD ▸ hm p H)
          next H=> exact hu p (by simpa using H) hv Wi rfl rfl _ _ (hn p (by simpa using H)))
end YM.Massive.Tarn.Quilt
#print axioms YM.Massive.Tarn.Quilt.twin
