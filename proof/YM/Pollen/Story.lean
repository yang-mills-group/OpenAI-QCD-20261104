import YM.Pollen.Gambit
import YM.Clays.Benny
import YM.Clays.Acer
import YM.Bister.Body
import YM.Pollen.Oak
import YM.Helio.Ribbons
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.Sample.Basal
open QCD QCD.Grass QCD.Cove Lattice Finset Ribbon Cupola Stew
open Function Lattice Wilson Creek Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph QCD.GasP PhysicalNext.Repeat.Turn Patron Kites Ribbon Cupola Plate Plate.Card Relight Ruby Massive.PCAC
open scoped Topology BigOperators ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c:Side}{N k:ℕ}{I D:Type}[Fintype I]{a t b w x v θ m:ℝ}
variable (o:I→Site c) {U:BudgetPoint}
variable (V: I→Grid c→ Fields c N→L[ℂ]Fields c N) (H:∀ i,Suit (o i) U a (V i)) (d:I→ℂ) (s:List I)
local notation "P"=> Patio (Keys c N⊕Spine I)
local notation "S"=>Support c
local notation "q"=> traceI I
set_option quotPrecheck false
local notation "Φ" X:arg=> effU (fun k=> V k X) (fun k=> (H k).bean X) d
local notation "Ω" X:arg=> actU (fun k=> V k X) (fun k=> (H k).bean X) d
include H
open Stretch
local notation "μ₀"=> ample N I
variable (F :Patron.Rail c (ample N I) D)
local notation "L"=> withdraw N o t
local notation "R"=> banknote N o t
local notation "qT" i:arg=> (F.addr i).place
omit H
local notation "K"=> furtherK o V H d s F t
local notation "Z"=> roofV o s F
local notation "E"=> MotK o s F
local notation "ρμ" j:arg=>beamFee U.B j
include H
variable (h: Wage.Tip N o (traceI I) F U t b v)(ht:0 < t)
include h ht
variable (htV:1 ≤ v)(hu:1 ≤ t)(hb:0 ≤ b)(hr:s.Nodup)
include hr
variable {T Q ε ρ:ℝ}
local notation "gΦ" i:arg=> s.filter (fun j=>j∈ (i:Finset I))
open Trees
variable (ha :1 < U.B*U.B)(X:Grid c)(M:Finset I)(he:Spaced o M U.B)
local notation "Xs"=> shutter (Keys c N) M
local notation "G"=> Basin K Z U.threshold
local notation "gP"=>Orig K Z
include ha he htV hu hb
lemma valueZ (hw:Quits (K) U.B ρ T w t)(hz:1 ≤ T)(h0:0 ≤ w) :Xs ((Ω X) s (L (heartK F U.threshold X)))=Xs (L (heartK (G) U.threshold X)):=by
    rw [dreamed K Z (aliveK o V H d s F h ht) hz h0 hw hu X]
    let A:=(Xs).comp L; let B:= (Xs).comp (((Ω X) s).comp L); let f i:= F.warp i X; let g i:= (gP).warp i X; let l:= flags U.threshold X
    have hx : Summable (fun i=>‖f i‖):=Ruby.income _ _ hu htV h.tilt.sold hb; have hy:Summable (fun i=>‖g i‖):= Ruby.income K _ hu hz hw h0; change B (∑' i,tK F U.threshold X i) = A (∑' i,tK (gP) U.threshold X i); simp_rw [termsK]; rw [Film.stamps F.addr _ _ B hx,Film.stamps _ _ _ A hy]; rw [catalogue F.addr (B ∘ f) _ (Film.payable B.toLinearMap.toContinuousLinearMap hx),catalogue Z (A ∘ g) _ (Film.payable A.toLinearMap.toContinuousLinearMap hy)]; apply congr_arg (fun d:Hat c→P=> ∑' i,Plate.roof id d l i); funext T
    let x:=A∘ g; let V1:D→ P:= A∘ f; let V2:E→P:= x ∘ Sum.inr; have h1 :=Film.payable A.toLinearMap.toContinuousLinearMap hx; have h2:Summable (fun i=> ‖V2 i‖):=Film.payable A.toLinearMap.toContinuousLinearMap (hy.comp_injective Sum.inr_injective)
    have h_rr : x=Sum.elim V1 V2:=funext fun x=> by cases x <;>rfl
    change Plate.coin _ _ _=Plate.coin Z x T; rw [h_rr,roofV,show Plate.coin _ _ _=_ from (Film.coin_merge F.addr (F.addr∘Sigma.fst) V1 V2 h1 h2 T:Plate.coin Z (Sum.elim V1 V2) T= _),fingerprint,fingerprint,fingerprint]
    let p (i:D):= if F.addr i=T then V1 i else 0; let q'(i:E):= if F.addr i.1=T then V2 i else 0; have ht₁ : Summable p:= Film.aloneC F.addr T V1 h1; have ht₂: Summable q':= Film.aloneC _ T V2 h2 -- annotate
    change (∑' i:D,(if F.addr i=T then B (f i) else 0))=(∑' i,p i)+∑' i,q' i; rw [ht₂.tsum_sigma,← ht₁.tsum_add (ht₂.sigma)]; apply tsum_congr; intro i; unfold p; split; next hT=>
                                                                                                                                                                                        rw [tsum_fintype]; unfold q'; simp only [hT,ite_true]; exact plaque o V H d s F h ht hr ha X M he i -- hr shadow binder
    symm; rw [tsum_fintype]; simp [q', *] -- split `d` local hr
omit he
variable (Y:Patron.Rail c N D) {J:Type} (Z':Patron.Rail c N J) (hR:Correspond (faultK N o t F) Z')
variable {A A':ℝ}
include hR
lemma audited (hv:1 ≤ T)(hw:Quits (K) U.B ρ T (A+A') t)(h_t:0 ≤ A)(hy:0<A')(hx:0<ρ)(ht':degreePrice U.B ρ A' ≤ Q)(hq:Q<1)(huv:ρ *(1-Q)⁻¹ ≤1) : Wage.Tip N o q (G) U t A T ∧ Correspond (faultK N o t (G)) Z' ∧∀ (X:Grid c)(s':Finset I),Spaced o s' U.B→shutter (Keys c N) s' ((Ω X) s (L (heartK F U.threshold X)))=shutter (Keys c N) s' (L (heartK (G) U.threshold X)):=by
    have hk := aliveK o V H d s F h ht
    have hh(K':D⊕E)(X):Well N o t q ((K).warp K' X):=by cases K'; exact h.fits ..; exact (paneK o V H d s F h ht ..).1
    have hp:= supportTip N o q K Z hk hh hw hv h_t hx hy hq ht' huv; let e : D ↪ (D⊕E):=⟨Sum.inl,Sum.inl_injective⟩
    refine ⟨hp,cring N o K Z e F (fun i=>rfl) (fun _=>rfl) (fun _=>rfl) ?_ Z' hR h.tilt.uses (fun i=> Ruby.income _ _ hu hv hp.tilt.sold h_t), (fun X s h'=>valueZ o V H d _ _ h ht htV hu hb hr ha X s h' hw hv (add_nonneg h_t hy.le))⟩ -- h.w order.fix
    · rintro (i|j) he X; exact False.elim (he ⟨i,rfl⟩); exact (paneK o V H d s F h ht ..).2.2
end YM.MassiveQCD.Sample.Basal
#print axioms YM.MassiveQCD.Sample.Basal.audited
