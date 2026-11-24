import YM.Fir.Chest
/-! Exact quotients all conventions; Ranger caps. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Fir
open YM.Fir YM.Fir.Mesh YM.Fir.NoteF Needle Needle.GaugeP Filter Set Function Metric
open Lattice Cells QCD QCD.Lat Patria Patria.Depth Patria.Hub
open UV Poised Plans Plans.Stamp Intag.Vale
open scoped Topology BigOperators Classical
variable {C:Sequence} {P:Calibration C} {G:∀ d,Cottage P d} {β e:ℝ}(hp:C.Path β e)(hr:Sway C.S) {n:ℕ} {φ:ℕ→ℕ}(hφ:Tendsto φ atTop atTop)
namespace Sash
variable (s:Sash G φ)
variable {Z:SpaceZ}(H:Ability P φ Z)
-- these proper. echo.Injects
lemma voiceL {Α X Y:Type*}[NormedAddCommGroup X][NormedSpace ℂ X][NormedAddCommGroup Y][NormedSpace ℂ Y] {F:Filter Α}{f:Α→ X→L[ℂ]Y}{g:X→L[ℂ]Y}(h:Tendsto f F (𝓝 g)){u:Α→X}{z:X}(ht:Tendsto u F (𝓝 z)):Tendsto (fun i=> f i (u i)) F (𝓝 (g z)):=by
    let T: ((X→L[ℂ]Y) × X)→ Y:= fun x=> x.1 x.2; have hv:Continuous T:=by unfold T; fun_prop
    exact (hv.tendsto (g,z)).comp (h.prodMk_nhds ht)
include hp hr hφ
lemma rich (d:ℕ)(u:Averaging):Surjective (s.A u d):= (G d).roles hp hr u φ hφ _ (s.plumes u d)
lemma rolled (d:ℕ)(z:CellF d): s.A none d (s.R d z)=z:=by
    let p(i:ℕ):=(G d).plate none i (ridgeF G d i z)
    have hx : Tendsto (fun i=>p (φ i)) atTop (𝓝 (s.A none d (s.R d z))):=voiceL (s.plumes none d) (voiceL (s.pearls d) tendsto_const_nhds)
    have he:∀ᶠ i in atTop,z=p i:=by
        filter_upwards [servesR hp (G d).K hr (G d).rise (G d).E] with i hi
        specialize hi z 0; have hz:mover P d i none (ridgeF G d i z)=ridgeF G d i z:= (P.mix d none i).symm_apply_apply _; change z= tip (G d).K (G d).E i (mover P d i none (ridgeF G d i z)); rw [hz]; have he:=hi.1; rw [map_zero,add_zero] at he; exact he.symm
    exact tendsto_nhds_unique hx (tendsto_const_nhds.congr' (show (fun _=>z)=ᶠ[atTop] (fun i=>p (φ i)) from hφ.eventually he))
omit hp hr hφ
variable (D:Fin n→ℕ)(u:Fin n→Averaging)
noncomputable abbrev pointsR (d:ℕ)(u:Averaging):Label d→ₗ[ℂ]Label d:= (s.R d).toLinearMap.comp (s.A u d).toLinearMap
noncomputable abbrev sage (s:Sash G φ) (Z:SpaceZ)(D:Fin n→ℕ)(u:Fin n→Averaging)(x:Points n):MultilinearMap ℂ (fun j=> Label (D j)) ℂ:= (Z n D x).compLinearMap (fun k=> s.pointsR _ (u k))
include hp hr hφ
-- one argument correspondence on ALL side assignments.
set_option maxHeartbeats 360000 in
lemma bouquet (U V:Fin n→(i:ℕ)→stalk C i) (h:∀ i,LightP C (U i)∧LightP C (V i)∧DimP C (U i-V i)) (x:Points n)(hx:x∈conf n):Exposes C φ (fun i p=> aperture C U (φ i) p-aperture C V (φ i) p) x 0:=by
    let T (p:Finset (Fin n))(k:Fin n):= if k∈p then U k else V k
    have he(p:Finset (Fin n)): Exposes C φ (fun i q=> aperture C (T p) (φ i) q-aperture C V (φ i) q) x 0:=by
        induction p using Finset.induction_on with
        | empty=>
             rw [show T ∅=V from by ext1; simp [T]]; simp only [sub_self]; exact tendsto_const_nhds
        | insert k p hk ih=>
             have hh:=carbon hp (T p) (U k-V k) k hr hφ x hx (h k).2.2 (fun i hi=>by unfold T; split_ifs; exact (h i).1; exact (h i).2.1)
             have hv:=hh.add ih; rw[zero_add] at hv
             refine hv.congr ?_; intro q; let i:=φ q.1; let b:=q.2; let L:= readZ (C:=C) i k b (fun j=> T p j i); have hu(j):T (insert k p) j=(update (T p) k (U k)) j:=by by_cases h:j=k; subst j; simp [T]; simp [T,h]
             change tube C (T p) k (U k-V k) i b+(aperture C (T p) i b-aperture C V i b)= aperture C (T (insert k p)) i b-aperture C V i b; rw [funext hu]; change tube _ _ _ _ _ _+(_-_)=tube _ _ _ _ _ _-_
             rw [meters,meters,Pi.sub_apply,map_sub,show readZ (C:=C) i k b (fun j=> T p j i) (V k i)= aperture C (T p) i b from ?_]; abel
             apply congr_arg (fun u=> readS C i u b); funext j; by_cases h:j=k; · subst j; rw [update_self,show T p k= _ from if_neg hk]
             rw [update_of_ne h]
    simpa [show T Finset.univ=U from by ext1; simp [T]] using he Finset.univ
include H
variable (v:(j:Fin n)→Label (D j)) (x:Points n)(hx:x∈conf n)
include hx
lemma guide : Exposes C φ (fun i p=> eyeW P D u (φ i) p v) x ((sage s Z D u x) v) :=by
    let U(k:Fin n)(i):=stemV P (D k) i (u k) (v k); let Y(k:Fin n)(i):=(G (D k)).plate (u k) i (v k); let V(k:Fin n):= glass G (D k) (Y k)
    have hz:= bouquet hp hr hφ U V (fun i=>by
         have ht:= (G (D i)).pointsP hp hr (u i) (fun _=> v i) ⟨_,norm_nonneg (v i),Eventually.of_forall fun _=> le_rfl⟩; refine ⟨ht.1,Fir.lively hp G hr _ _ ?_, ht.2⟩; obtain ⟨T,hT,H⟩:= (G (D i)).heights hp hr (u i); exact ⟨_,mul_nonneg hT (norm_nonneg (v i)), H.mono fun k hk=> ((Cottage.plate ..).le_opNorm _).trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))⟩) x hx -- infer
    let Q(i:ℕ)(k:Fin n):= ridgeF G (D k) (φ i) (Y k (φ i)); let w(k:Fin n):= s.R (D k) (s.A (u k) (D k) (v k))
    have he:Tendsto Q atTop (𝓝 w):= tendsto_pi_nhds.mpr fun k=> voiceL (s.pearls _) (voiceL (s.plumes ..) tendsto_const_nhds)
    have hV:Exposes C φ (fun i b=> aperture C V (φ i) b) x (Z n D x w):= Ability.turns D w H Q he _ hx -- order args
    have ht:=hz.add hV; rw [zero_add] at ht; change Exposes C φ (fun i b=> aperture C U (φ i) b) x (Z n D x w); exact ht.congr (fun i=> sub_add_cancel ..)
omit hp hr hφ
end Sash
end YM.Massive.Fir
#print axioms YM.Massive.Fir.Sash.rolled
#print axioms YM.Massive.Fir.Sash.guide
