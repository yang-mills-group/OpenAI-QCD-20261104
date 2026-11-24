import YM.Elms.Pivots
import YM.Differ.View
/-! # turn grouped fees for support and curvature limits.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Elm
open QCD QCD.Lat Lattice Wilson UV UV.Free TensorProduct Function
open QCD.Grass Poised Poised.Display Poised.Sieve Poised.Plans MeasureTheory Filter Finset
open scoped Topology BigOperators TensorProduct Pointwise Classical ContDiff Stamp
open Papyrus.Purl Papyrus LoomC
variable {d:ℕ}
namespace SparK
open Push.Mark YM.Source YM.Source.Drops RG RP
namespace Arbor
open Lining Lining.Temper Poised.Carte.Hem Permit Patria Exposure
variable {n:Side}(U:Grid n)(P : Regulator n 6)
variable (o:Cover)(w v:Walk)(e:Point)(a:Axis)
namespace Gallery
open QCD.Kites PrismD Civic
open Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate
open Cove Creek
-- Practical estimates for any Draft. No invariance here. Include base budget.Pi
lemma lease_sight (S:Stenc)(F:Cylinder.Formula S 6)(s g k m r j:ℕ)(h:Lease r k m g (fun Y=> porch S Y F))(hS:used_bound S r)(he:∀ Y:Land, porch S Y F∈layer (Pairs (Cylinder.Nearest S 6)) s): ∃ t:ℝ,0≤t∧∀(b:Cover)(B:BudgetPoint)(n:Side), B.power=m→ B.order=k→ 2*(r+1)<n.val→∀ v:ℝ,0<v → Sight (pot (r+1) n b) (wrap n b) j B v ⇑(grant S F n b) (t*levy g s B.threshold v):=by
   obtain ⟨C,hC,h⟩:=h; let D:ℝ:=(1+(r:ℝ))^j
   refine ⟨D*C, mul_nonneg (by unfold D; positivity) hC, fun b B n hP hO hr v hx=>?_⟩; let L:=fun Y:Land=>porch S Y F; let o:=wrap n b; let f:= L∘expandAt o; have hL:= h B n o hr hP
   let M:= ((tongue (c:=n) S b).toLinearMap.restrictScalars ℝ).toContinuousLinearMap; have he' : ⇑(grant S F n b)=M ∘ f:=rfl
   rw [he'];
   have ht:LocalOn (S:Set Cover) L:=by intro u w he; dsimp only [L]; unfold porch; rw [show Source.entry u (S:=S)=Source.entry w from funext fun i=> by unfold Source.entry; rw [he _ i.1.property.1 i.1.property.2]]
   have hX:LocalOn (S.image (fun i=>wrap n i + o)) f:=by simp only [Finset.coe_image]; exact LocalOn.expandAt (S:Set Cover) L ht o
   have h' : pot r n b⊆pot (r+1) n b:= Corona.halo_mono (by omega) (Finset.Subset.refl _); have hw (T:Grid n): Push.Local.Chart B.order f T:=(hL.smooth [] (Nat.zero_le k) T).contDiffAt.of_le (by norm_cast; simp)
   have hB : LocalOn (pot (r+1) n b) f:= fun i j hj=> hX _ _ (agrees_mono hj (halos S (r+1) (by omega : r ≤ r+1) o hS))
   refine ⟨fun i j hp=>congr_arg M (hB i j hp),fun i=>Creek.regionMon (Cove.limitsMon _ _ h') (ranch _ b (f i) hS),fun i _=> M.contDiff.contDiffAt.comp _ (hw _),fun i hi l hp ho=> ?_, ?_, by unfold D levy; positivity [B.threshold_pos]⟩
   swap; · rw [←he']; exact (grant S F n b).continuous.measurable
   rw [Push.Local.left_linear M l (hw i) hp]; let y:=RG.leftDerivs f l i
   let N:= Pairs (Cylinder.Nearest S 6); have hκ:y∈layer N s:=by
        let P:= ((Stew.panel (D:=N) s).restrictScalars ℝ).toContinuousLinearMap
        have hv : P∘f=f:=funext fun i=> (Stew.past s s (he (expandAt o i))).trans (if_pos rfl)
        have ht : P y=y:=by unfold y; rw [← Push.Local.left_linear P l (hw i) hp,hv]
        rw [← ht]; exact Stew.chamber _ y
   have ht' := hL.bound l (hO ▸ hp) ho i hi; rw [one_pow, mul_one] at ht'
   exact (pennyT S b j y hS v hx hκ).trans ((mul_le_mul_of_nonneg_left ht' (by positivity)).trans_eq (by unfold D levy; ring))
lemma lease_flame (X:Drape)(g s:ℕ) (hx:Draft X g s): ∀ᶠ r:ℕ in atTop,∀ k m w j:ℕ,∃ C:ℝ,0≤ C ∧∀ (P:BudgetPoint)(c:Side)(o:Cover)(v:ℝ),0<v → P.power=m→ P.order=k→ 2*(r+1)< c.val → Flame (X c o) P (pot (r+1) c o) (wrap c o) v w j (C*levy g s P.threshold v):=by
    obtain ⟨S,ht⟩:=hx.exists; obtain ⟨F,rfl,hF,hX⟩:=ht.funded; filter_upwards [Permit.eventual S] with r hr k m w j; obtain ⟨C,hC,h⟩:=lease_sight S F s g k m r 2 (hX k m r hr) hr hF
    let V:= ((1+(↑(r+1):ℝ))^w)^j; refine ⟨V*C,mul_nonneg (by unfold V; positivity) hC,fun P c o v hv he ht hO=>?_⟩; rw [mul_assoc]; exact extended (h o P c he ht hO v hv) (fun i=> placed_s _ i _) hv _ _
lemma lantern (x:Drape)(g s:ℕ)(h:Draft x g s):∃ C:ℝ,0≤C∧∀(v:ℝ),0<v →∀ (n:Side)(b:Cover)(V:Grid n), Creek.load (fun _=>v) (x n b V) ≤ v^s*C:=by
    obtain ⟨S,ht⟩:=h.exists; obtain ⟨F,rfl,hF,h'F⟩:=ht.funded; let f(i:Land):=porch S i F; obtain ⟨C,hC⟩:= (show Continuous f from porch_c ..).bounded_above_of_compact_support (HasCompactSupport.of_compactSpace _)
    refine ⟨C,(norm_nonneg _).trans (hC 1),fun v hv n b V=>?_⟩; have he:=convoy h V b; let k:= grant S F n b V; have hz : ‖k‖ ≤ C:= (tongue_pay S b _).trans (hC (expandAt _ _));
    apply le_trans (b:= v^s * ‖k‖) _ (mul_le_mul_of_nonneg_left hz (by positivity)); change Brick.dryL v k≤_; rw [Brick.ledgers _ hv]; apply le_of_eq; rw [Grass.norm_def (_:Lat.Fields n 6), Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; by_cases hp:i.card=s; · rw [hp]
    rw [Grass.spectrum he i hp]; simp
-- tags.P at boot, any translation Tally support.Refresh for orientation.X.Y
lemma rover (H:SourceRead.TaperHol)(U:Hol su)(x:Drape)(g s d:ℕ)(hX:Profile x)(hx:x∈phrase g s):∃ p: Label d, TravelsP H x (passport d p):=by
    have h:=shelf hx; obtain ⟨p,M,hM⟩:= peony H U x g s d (whereby_self x ▸ h.draws 1); let n:Side:=⟨M+1,Nat.succ_pos _⟩; have hv(u:su.El): tint u d p=p:=by
       obtain ⟨N,hN⟩:= travelsZ H p u ⟨M,hM⟩; let n:Side:=⟨M+N+1,Nat.succ_pos _⟩; have hz: whereby u x=x:=funext fun n=> funext fun o=> hX _ _ (gways u n); rw [hz] at hN; let o:Cover:=0; exact Subtype.ext (Beacon.chooses H o (Submodule.coe_mem (tinted d u p)) p.property (hN n o (by change N ≤ M+N+1; omega)) (hM n o (by change M ≤ M+N+1; omega)))
    let q: Label d:=⟨_,(label_law p.val).mpr ⟨p.property, fun u=> congr_arg Subtype.val (hv u)⟩⟩; exact ⟨q,M,hM⟩
lemma typedW (H:SourceRead.TaperHol)(p:Label d)(V:Knot p)(h:Requisite H p V):∃ y:Label d, TravelsP H V.X (passport d y) ∧ Tendsto (fun t:ℝ=> ((↑(t^V.g):ℂ))⁻¹ • prism t 1 d (passport d y)) (𝓝[>] 0) (𝓝 (passport d p)):=by
     obtain ⟨q,⟨K,hK⟩,ht⟩:= h.spectrum.grantX; obtain ⟨U⟩:= Source.Hol.exists_ode su; obtain ⟨y,M,hz⟩:=rover H U V.X _ _ d h.hasi h.mantle; refine ⟨y,⟨M,hz⟩,?_⟩; let N:Side:=⟨M+K+1,Nat.succ_pos _⟩; rw [show passport d y=q from Subtype.ext (Beacon.chooses H 0 (Submodule.coe_mem (passport d y)) q.property (hz N 0 (by change M≤M+K+1; omega)) (hK N 0 (by change K≤M+K+1; omega)))]; exact ht
end Gallery
end Arbor
end SparK
end YM.Massive.Elm
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.lease_flame
#print axioms YM.Massive.Elm.SparK.Arbor.Gallery.typedW
