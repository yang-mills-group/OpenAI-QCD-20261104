import YM.Elms.Pacing
import YM.Differ.Ephemeral
/-!
# Package a single support finite-stencil operator into ancestor receipt.
Earn negatives genuinely. This costs the actual horizon projection.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised.Plans.Stamp
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place Module TensorProduct
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {u s t a θ v A' D C ν Θ Ω α β φ:ℝ}{k d n j l m r:ℕ}{c:Side}
open Pipes Lining Lining.Ferry Lining.Temper Collage
open Pressure Garden Run Laurent Carrier Next.Free
open Beacon MultiNext.SignedSource Stative
open Counting Counting.Click Terrain Display Costs Sieve Chute Papyrus Facets Orientation Carte.Hem
open QCD.Kit MassiveQCD.Plate Card Iris QCD.Cove QCD.Kites QCD.Stew Push.Local Push.AbsoluteSums
open Stamp QCD.Loom QCD.Loom.Fleet Puff MassiveQCD.Ribbon MassiveQCD.Cupola MassiveQCD.Lyre Girdle Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery -- ?
open Elm Elm.SparK Elm.SparK.Arbor
variable (H:TaperHol){U:Hol su}(A:Exhibit U)(b:Cover)(x:Label d)
local notation "o"=> wrap c b
variable (p: Insertion c 6)(v w z:ℝ)(Pt:BudgetPoint)
-- large but single.PowerP and κ package. omit Economy constants later
open QCD.Creek
lemma floss_add(L N:Density c 6)(V: Grid c): load (fun _=>v) ((L+N) V)≤ load (fun _=>v) (L V)+load (fun _=>v) (N V):=by simp only [Creek.load,Creek.wscale,Pi.add_apply]; rw [map_add]; exact norm_add_le ..
structure Volume (b:Cover)(r0:ℕ)(F:Density c 6)(x:Label d)(k l:ℕ)(q:Bool)(a s v Φ Ω Ξ:ℝ) : Prop where
   funded :∃ V:CentreFrame (c:=c) Pt v x q A b (r0+1) Unit Empty, Published V H k l a s Φ Ω ∧ Courtesy A b x q Pt V 4 Ξ ∧ spineV A b x q Pt V=F
variable (q:Bool)
lemma gain (hp:Pilot H A d m k n j r α β) (hm:Pt.order=m)(hk:Pt.power=k)(R r₀:ℕ) (hr: r ≤ R)(hr₀:r₀≤R+1)(hB: R+1 ≤ Pt.B)(hC:30*(r+1) ≤ c.val) (ht:0≤ t)(hv:1≤ v)
     (h: ActionTest H b p x.val)(ho: Lat.Invariant p) (hq: Gallery.moon q p)
     (hl: Flame p Pt (pot r₀ c b) o v n j w)(hV:∀ U:Grid c, Creek.load (fun _=>v) (p U) ≤z)(hF:∀ y:Label d,∀ U:Grid c, Creek.load (fun _=>v) (graphs d A b y U) ≤ C*wealth y.val Pt.threshold v)
     (hW:0≤C) (ha:0 ≤ Ω) (φ ξ:ℝ) (hΦ:(w+β*(wealth x.val Pt.threshold v))*Real.exp (81*t) ≤ φ)(hΩ: (z+2*(C*wealth x.val Pt.threshold v))*Real.exp (4*81) ≤ ξ): Volume H A Pt b r (c:=c) p x n j q t s v φ Ω ξ:=by
    let Q: Density c 6 := graphs d A b x; let f:Density c 6:= ⇑p-Q; let o':=wrap c b; have he:= actor H b p q x h hq -- signature
    let B:=wealth x.val Pt.threshold v
    have hh₁: Flame Q Pt (pot (r+1) c b) o v n j (β*B):=hp.bill _ _ _ v _ hm hk (by omega) (by positivity);
    have hF' : Flame f Pt (pot (R+1) c b) o v n j (w+β*B):=by
         unfold f; rw [sub_eq_add_neg,← neg_one_smul ℂ Q]; have hz:= flare_by Pt _ Q hh₁ (-1); -- inspect
         simp only [norm_neg,norm_one,one_mul] at hz; exact flare_add _ _ _ _ (across hl _ (Corona.halo_mono hr₀ (Finset.Subset.refl _))) (across hz _ (Corona.halo_mono (by omega) (Finset.Subset.refl _))) (by linarith)
    let Y:Puff c 6 Unit q:=⟨fun _=>site_p b (R+1),fun _=>f,fun _=> ?_⟩
    swap; · intro i; change Grass.Hom q (f _); unfold f; simp only [sub_eq_add_neg,Pi.add_apply,Pi.neg_apply]; rw [← neg_one_smul ℂ (Q _)]; exact (hq _).add ((show Grass.Hom q (Q _) from graphing d A b x q he i).smul _)
    let M:= (Film.mk (c:=c) (N:=6) (I:=Unit) (U:=Empty) (fun e=>e.elim) (fun i=>i.elim) (fun i=>i.elim)); let V:CentreFrame Pt v x q A b (r+1) Unit Empty:=⟨he,Y,M⟩
    let nc:= coverNumber Pt.B (pot (R+1) c b); let nk:= coverNumber Pt.B (pot (r+1) c b)
    have hc:nc≤81:= (Corona.cover_mono (Corona.halo_mono (show R+1≤1*Pt.B by rw [one_mul]; exact hB) (Finset.Subset.refl _)) _).trans (Corona.tile _ 1 _ Pt.B_pos); have hm:nk≤nc:=Corona.cover_mono (Corona.halo_mono (by omega) (Finset.Subset.refl _)) _
    refine ⟨V,⟨⟨fun _=>rfl, fun _=>hF'.sight.room,fun _=>hF'.sight.borel,?_,fun i=> hF'.sight.gate⟩, ⟨fun _=>w+β*B,fun i=>hF', ?_⟩, ⟨fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun i=>i.elim,fun i=>i.elim⟩, ⟨fun _=>0,fun i=>i.elim,fun q=>⟨fun i=> Empty.elim i,Summable.of_finite,(tsum_empty).trans_le ha⟩⟩,fun i=>?_⟩,?_,?_⟩
    · intro i U g; change Lat.slots 6 g (p _- Q _)= f U; rw [map_sub,show Lat.slots 6 g (p _)=p U from DFunLike.congr_fun (ho g) U, show Lat.slots 6 g (Q _)=Q U from graphite ..]; rfl
    · apply Iris.spend_collect _ _; refine ⟨fun i=> mul_nonneg hF'.sight.travels (Real.exp_nonneg _),Summable.of_finite,?_⟩; rw [tsum_fintype,Fintype.sum_unique]; exact (mul_le_mul_of_nonneg_left (Real.exp_monotone (show t*nc≤81*t by rw [mul_comm (81:ℝ)]; gcongr; exact_mod_cast hc)) hF'.sight.travels).trans hΦ
    · change ActionTest H b f 0; have h0:= acting H b d Q x.val (hp.tested _ _ x hC) (-1); have he:= actsPlus H b d _ _ _ _ h h0; rw [neg_one_smul ℂ Q,neg_one_smul ℂ x.val,add_neg_cancel] at he; unfold f; rw [sub_eq_add_neg]; exact he
    · have hv:0≤z:= (Creek.load_nn ..).trans (hV (1:Grid c)); have hb:0≤ B:=wealth_ge ..; let U:=Jars d; let g(i:U):=C*wealth (gradeCut d i.val x).val Pt.threshold v
      refine ⟨Sum.elim g (fun _=>z+C*B),fun i=>?_,fun i T=>?_,?_⟩ -- addresses.Power total
      · cases i; exact mul_nonneg hW (wealth_ge ..); exact add_nonneg hv (mul_nonneg hW hb)
      · cases i with
        | inl i=> exact hF .. -- neglect `≤`
        | inr i=> change Creek.load _ (f T) ≤ _; unfold f; rw [sub_eq_add_neg,← neg_one_smul ℂ Q]; have hp := floss_add v ⇑p ((-1:ℂ) • Q) T; simp only [Pi.smul_apply, Creek.load_scale,norm_neg,norm_one,one_mul] at hp; exact hp.trans (add_le_add (hV T) (hF x T))
      rw [Fintype.sum_sum_type,Fintype.sum_unique (ι:=Unit)]; apply le_trans _ hΩ; change (∑ i:U, g i*Real.exp (4*nk))+(z+C*B)*Real.exp (4*nc) ≤ _; rw [←sum_mul]; unfold g; rw [←mul_sum,← coinsS]; change C*B*Real.exp _+ (z+C*B)*Real.exp _ ≤ (z+2*(C*B))*_; rw [show z+2*(C*B)= C*B+(z+C*B) from (by ring),add_mul (C*B)]; apply add_le_add
      · refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (mul_nonneg hW hb); exact_mod_cast (Nat.mul_le_mul_left 4 (hm.trans hc))
      refine mul_le_mul_of_nonneg_left (Real.exp_monotone ?_) (add_nonneg hv (mul_nonneg hW hb)); exact_mod_cast (Nat.mul_le_mul_left 4 hc)
    funext i; rw [spineView,Fintype.sum_unique]; change Q i+((p i)- Q i)=_; abel
end YM.Massive.Poised.Plans.Stamp
