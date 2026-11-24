import YM.Poised.Canoe
/-! High uniform reserve with retarget after true spinStencil. Position debt through mass tapes even for true origin. Series.P.Phase.Price planes keep AP. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Lattice Wilson RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B A X E : Type}{d a k n m r:ℕ}{c l:Side}
namespace Pipes
open Set Cedar Ember Oval Cove Creek Stew PhysicalNext.JointLoad MultiNext.SignedSource MultiNext.SignedSource.Lyre Place Lining Lining.Ferry QCD.Brick
open YM.Next.Free Pressure Garden QCD.Fork Leaf Tee Flume Kit Run
variable (P:Flight n m)(D:l.val=c.val * P.L.val)
variable (b:Cover) [Fintype B]
local notation "Y"=> Alg B
open Laurent
abbrev capW (w:B→ℝ) (i:B→ℂ):ℝ:=∑ j,w j*‖i j‖
def purseX (a:Site c)(r:ℕ)(p:ℝ)(i:Faces (Site c)) := p*Heir.spine r (locationP i) a
lemma purse_pos (a:Site c)(r:ℕ)(p:ℝ)(hp:0<p)(i:Faces (Site c)):0<purseX a r p i:= mul_pos hp (Heir.spine_pos ..)
lemma towns (d:ℕ)(h:n ≥4)(h':m≥4):∃ C:ℝ,1≤C∧∀ (c l:Side)(P:Flight n m)(H:l.val=c.val*P.L.val) (p:List Axis),p.length ≤ n-2 →∀ b:Cover,∀ x: Cover,∀ i:Pipes.Shell,∀ t:ℝ,0<t →
   let X:= oldDiff (proton P H) p
   let j:= rowsA b (flareV X) x i; let L:= (P.L.val:ℝ)⁻¹
   capW (purseX ((sliceL P H).parent (wrap l b)) d t) j ≤ C*Kit.slope P.L*t*L^(1+p.length)*(1+L*size x)^d :=by
    obtain ⟨C,hC,hK⟩:= caperHigh h h' d; refine ⟨1+stemF 6*C* (3:ℝ)^d, le_add_of_nonneg_right (by unfold stemF Jets.Sun.fingers; positivity),?_⟩
    intro c l P H p hp b x i t ht X j L
    let R:=sliceL P H; let f:=wrap l b; let z:=wrap l (x+b); let U:=1+L*size x; let o:=R.parent f; let h₀(q:Site c):=Heir.spine d q o; have hL : 0<L:=by unfold L; positivity
    have he (j:Site c): h₀ j ≤ (3:ℝ)^d*U^d * meets R z d j:=by
        have ht:separation z f ≤ size x:=by
           unfold separation z f; rw [map_add, add_sub_cancel_right]; exact Newt.wrapped ..
        have hp' : ↑(R.count.val) * (separation (R.parent z) o:ℝ) ≤ (size x:ℝ)+R.count.val:=by exact_mod_cast (Corona.foreshorten R z f).trans (Nat.add_le_add_right ht _) -- namespace
        have hd:(separation j o:ℝ)≤ separation j (R.parent z)+(separation (R.parent z) o:ℝ):= Nat.cast_le.mpr (separation_triangle ..)|>.trans_eq (Nat.cast_add ..)
        have hy:1≤U:=le_add_of_nonneg_right (mul_nonneg hL.le (by positivity))
        unfold meets; rw [separation_comm (R.parent z)]; rw [← mul_pow, ← mul_pow]; apply pow_le_pow_left₀ (by positivity); have ha : (separation (R.parent z) o:ℝ) ≤ U:= le_trans (le_of_eq (by rw [← mul_assoc L,show L*(R.count.val:ℝ)=1 from inv_mul_cancel₀ (by positivity),one_mul] : _ = L*((R.count.val:ℝ)*(separation (R.parent z) o:ℝ)))) ((mul_le_mul_of_nonneg_left hp' hL.le).trans_eq (by unfold U; rw [mul_add,show L* (R.count.val:ℝ)=1 from inv_mul_cancel₀ (by positivity),add_comm]))
        nlinarith [Nat.cast_nonneg (α:=ℝ) (separation j (R.parent z))] -- hy.le invalid
    let p' (j:Keys c 6):= (3:ℝ)^d*U^d*meets R z d (locationP j)*t; unfold capW; apply le_trans (Finset.sum_le_sum (g:=fun j=> p' j*‖cell X z (locationP j)‖) (fun k _=>?_))
    · unfold p'; simp_rw [show ∀ y: ℝ,(3:ℝ)^d*U^d*y*t= (t*(3^d*U^d))*y from fun y=>by ring,mul_assoc ((t:ℝ)* _)]; rw [← Finset.mul_sum,crystals (fun i:Site c=> meets R z d i *‖cell X z i‖)]; have ht:= mul_le_mul_of_nonneg_left (hK P c l H p hp z) (show 0≤ stemF (6:ℕ) by unfold stemF Jets.Sun.fingers; positivity)
      refine (mul_le_mul_of_nonneg_left ht (show 0 ≤ _ from mul_nonneg (show 0≤t by positivity) (show 0≤ (3:ℝ)^d*U^d by unfold U; positivity))).trans ?_
      let N:= stemF 6*C*3^d
      calc
         _=N*Kit.slope P.L*t*L^(1+p.length)*U^d:=by unfold N L cape; ring
         _≤_:=by change N*Kit.slope P.L*t*L^(1+p.length)*U^d≤(1+N)*Kit.slope P.L*t*L^(1+p.length)*U^d; have he:=boxed1 P.L; have hx:=he.1; have hU:0 ≤ U:=by unfold U; positivity
                 gcongr; linarith
    have hh: locationP (stretch _ (z,i))= z:= life (z,i)
    refine mul_le_mul (b:=p' k) ?_ ?_ (norm_nonneg _) (by have h0:= meets_nn R z d (locationP k); unfold p' U; positivity); swap
    · change ‖ap _ _ * powerF X (stretch (Site l) (z,i)) k‖ ≤ _; rw [norm_mul,ap_one,one_mul]; exact (duty ..).trans (le_of_eq (by rw [hh])) -- rw recursive z argument
    exact (mul_le_mul_of_nonneg_left (he _) (by positivity : 0 ≤ t)).trans_eq (mul_comm ..)
end Pipes
end YM.Massive.Poised
