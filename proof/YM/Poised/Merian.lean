import YM.Poised.Sieve
/-!
# Placement of basis. No winding assumption outside the costed use.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson RG Source Source.Drops MeasureTheory Finset
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius TensorProduct Classical
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead Display Papyrus MassiveQCD.Plate QCD.Kites
variable {c : Side} {d k n : ℕ}
namespace Merian
open Beacon Next.Foundations Costs Lining Lining.Temper Ferry
open Collage
variable (H:TaperHol) (U:Source.Hol su)(b:Cover)(S:Finset Cover)
local notation "Ψ"=>Lat.Fields c 6
local notation "Z"=> SpinPol d
local notation "Σ'"=>Nearest S 6
def SmallT (c:Side)(S:Finset Cover)(r:ℕ) : Prop:= ∀ u ∈ S,∀ i:Axis,20*((u i).natAbs+r+2) ≤ c.val
lemma lift_gain (u:Cover)(hc:SmallT c S k)(hu:u∈S): lift (wrap c u)=u:=by refine lift_eq_iff.mpr ⟨rfl,fun i=>?_⟩; have h:= hc u hu i; omega
lemma taper_hall (u:Cover) {χ:Taper}(hc:SmallT c S k)(hu:u∈S)(a: Axis)(s:ℝ)(hx:s∈Ioo (-1:ℝ) 2) : χ.χ ((c.val:ℝ)⁻¹ • (vector u+s • basis a))=1:=by
   apply χ.near; intro i; have hp:(20:ℝ)*((u i).natAbs+(k:ℝ)+2) ≤ c.val:=by exact_mod_cast hc u hu i
   have ht: 0<(c.val:ℝ):= Nat.cast_pos.mpr c.property
   have hz: |basis a i| ≤1:=by simp only [basis]; by_cases he:a=i <;> simp [he,Ne.symm] -- norm
   change |(c.val:ℝ)⁻¹*((u i:ℝ)+s*basis a i)| ≤ _; rw [abs_mul, abs_of_pos (inv_pos.mpr ht)]; calc
      _ ≤ (c.val:ℝ)⁻¹*(((u i).natAbs:ℝ)+2):=by
         apply mul_le_mul_of_nonneg_left _ (by positivity); apply (abs_add_le ..).trans; rw [abs_mul]; apply add_le_add; swap; · apply (mul_le_of_le_one_right (abs_nonneg s) hz).trans; rw [abs_le]; exact ⟨by linarith [hx.1],hx.2.le⟩
         exact le_of_eq (by rw [Nat.cast_natAbs]; norm_cast) -- inspect
      _ ≤ _:=by rw [mul_comm,← div_eq_mul_inv,div_le_iff₀ ht]; linarith [Nat.cast_nonneg (α:=ℝ) k, Nat.cast_nonneg (α:=ℝ) (u i).natAbs]
lemma localFlare (p:Edge Cover)(hc:SmallT c S k)(hu:p.1∈S)(J:Labels.Jet su)(v:ℝ)(d:ℕ) : H.flow c d J v p 1= U.links (d/2) J (v^2) p:=by
   apply Source.Hol.agree (I:=Ioo (-1:ℝ) 2) (b:=0) isOpen_Ioo (convex_Ioo ..) (by simp) (A:=Source.partConnection (d/2) J (v^2) p) _ (fun t _=>(U.solves ..).2 t) ((H.solves ..).1.trans (U.solves ..).1.symm) (show (1:ℝ) ∈Ioo (-1:ℝ) 2 from ⟨by norm_num,by norm_num⟩)
   intro t ht; have hp:= (H.solves c d J v p).2 t; unfold Taper.connection at hp; rw [taper_hall S _ hc hu _ t ht,one_smul] at hp; exact hp -- arg proof
lemma exact_placement(c:Side)(b:Cover)(S:Finset Cover)(x:Cylinder.Formula S 6) (hc:SmallT c S k) (v:ℝ)(d:ℕ)(J:Labels.Jet su) : moment (c:=c) (d:=d) H b J (fun V=> places b x V) v = onStencil U x d J v :=by
   unfold places; unfold Beacon.moment onStencil; rw [adapt_together]
   have hg: Lattice.Agrees (S:Set Cover) (expandAt (wrap c b) (current H b d J v)) (U.links (d/2) J (v^2)):=by
        intro i hi hp; change views H b d _ _ = _; unfold views offset spark; simp only [add_sub_cancel_right,lift_gain S _ hc (show i.1∈S from hi)] -- inference
        rw [← focused]; exact localFlare H U S i hc hi J v d
   have he:Source.entry (S:=S) (expandAt (wrap c b) (current (c:=c) H b d J v))=Source.entry (U.links (d/2) J (v^2)):=funext fun i=> by unfold Source.entry; rw [hg _ i.1.property.1 i.1.property.2]
   unfold Cylinder.evaluate; rw [he]; suffices ht: lower (F:=6) (n:=c) (S:=S) b * Beacon.glow (c:=c) (d:=d) H.T b v = spinLink v by rw [ht]
   rw [show lower (F:=6) (n:=c) (S:=S) b = spar (fun i:↥S=> gain c b i.val) (fun i=>ap c (i.val+b) • 1) from table .., show Beacon.glow (c:=c) (d:=d) H.T b v=nacre (fun x y=> (spun H.T b x*profile y (offset b x) v) • 1) from ?_,spar_mul]; rotate_left
   · ext i j; rw [imprints]; simp only [Beacon.glow,Matrix.of_apply,Matrix.smul_apply,Matrix.one_apply,smul_eq_mul]; by_cases ht:i.2=j.2 <;> by_cases hh:i.1.2=j.1.2 <;> simp [ht,hh]
   rw [show spinLink (D:=S) (d:=d) v=nacre (fun x p => profile p x.val v • 1) from Germ.spinFace S v d]; congr 1; funext i y
   have hi: offset b (gain c b i.val)=i.val:=by unfold offset gain; rw [map_add,add_sub_cancel_right,lift_gain S _ hc i.property]
   have hx: spun H.T b (gain c b i.val)= ap c (i.val+b):=by
      unfold spun; rw [hi]; dsimp only; rw [show H.T.χ _=1 from ?_]; rotate_left; · simpa only [zero_smul,add_zero] using taper_hall (χ:=H.T) S i.val hc i.property timeAxis 0 (by constructor <;> norm_num)
      simp
   have hz(x:Cover): ap c x*ap c x=1:=by
      rw [ap,← prod_mul_distrib]; apply prod_eq_one; intro j _; rw [neg_one_zpow_eq_ite]; split <;> norm_num
   rw [hi,hx, Matrix.smul_mul, Matrix.one_mul,smul_smul,← mul_assoc,hz, one_mul]
lemma riseT (A:Exhibit U)(x:Label d)(hc:SmallT c (A.t d) k): ActionTest H b (fun V:Grid c=> places b (A.lead d x) V) x.val:=by
    intro J; rw [show moment (c:=c) (d:=d) H b J (fun V=> places b (A.lead d x) V) = onStencil U (A.lead d x) d J from funext fun _=> exact_placement H U c b (A.t d) _ hc _ d J]; exact Germ.seed (A.F d) (A.U d) (A.t d) J (A.sel d).extends_box _ _ (A.label d x)
end Merian
end YM.Massive.Poised
