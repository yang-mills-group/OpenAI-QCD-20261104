import YM.QCD.Globe.Over
import YM.QCD.Nola.Wheat
import YM.QCD.Nola.Arch
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Globe
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
open Revolve Villa Port Footprint AnalyticBridge.VerifiedReset Flume Pine YM.Next.Free Leaf LeafM Tee Garden Entr Kites
variable {f c:Side}{j k m N:ℕ}{S:Flight j k} {h:f.val=c.val*S.L.val}{p:BudgetPoint}
open Nola
variable (a:Flavor N) {w A b t:ℝ}
-- bilinear.Fee extracted all
noncomputable def stile (z:Finset (Keys c N))(X:EvenA c N)(t:ℝ):ℝ:= ‖coef z X.val‖*t^z.card
lemma goldO : ∃ C:ℝ,1≤C∧∀ (X:Bundle), ‖X‖≤ C*∑ i:Lat.Fiber,∑ j,‖X i j‖ :=by
    obtain ⟨b,hb,H⟩:= Sparks.float_norm; refine ⟨max 1 b,le_max_left ..,fun X=>?_⟩
    have hp(i j):‖X i j‖≤ ∑ i,∑ j, ‖X i j‖:=le_trans (single_le_sum (f:=fun j=> ‖X i j‖) (fun _ _=> norm_nonneg _) (mem_univ j)) (single_le_sum (s:=univ) (f:=fun i=> ∑ j,‖X i j‖) (fun i _=>sum_nonneg (fun _ _=>norm_nonneg _)) (mem_univ i))
    exact (H X _ (sum_nonneg fun i (_:i∈(univ:Finset Lat.Fiber))=> sum_nonneg fun _ _=> norm_nonneg _) hp).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (sum_nonneg fun i (_:i∈(univ:Finset Lat.Fiber))=> sum_nonneg fun _ _=>norm_nonneg _))
lemma intoA (m:ℕ) :∃ C:ℝ,1 ≤ C∧∀ (c:Side)(X:EvenA c N)(t A:ℝ), 0<t→ Cocoa X→GrassA X t m A→ Beam (feeF a X) m (t⁻¹^2*C*A):=by
    obtain ⟨C,hC,H⟩:=goldO; refine ⟨C,hC,fun c X t A ht hp hv=>?_⟩; let p:=feeF a X; let P:= univ (α:=Site c); have hQ:= hp.pick a
    refine centsT (x:=0) (fun i=>?_) hQ
    let r(v:Lat.Row c):Modes c N:= (v,a); let f (i:Lat.Row c ×Lat.Row c):=Stew.tag (r i.1) (r i.2)
    let F(z: Finset (Keys c N)):= grainH locationP X.val t m z; let V (x:Site c) y:= cell p x y
    have he (u v:Lat.Row c): F (f (u,v)) = ‖p u v‖ * t^2 * costS m u.1 v.1:=by
        change _= ‖bit (r u) (r v) *coef (f (u,v)) X.val‖ *_*_; rw [norm_mul, show ‖bit (r u) (r v)‖=1 from ?_, one_mul]; swap; · rcases bitS (r u) (r v) with he|he<;>rw [he]<;>norm_num
        unfold F grainH; rw [show (f (u,v)).card=2 from by simp [f,Stew.tag],show edges locationP (f (u,v))={v.1,u.1} from ?_,show Nola.tell ({v.1,u.1}:Support c) m=costS m u.1 v.1 from ?_]
        · change Nola.rodM _ _ _= _; rw [pairTell,costS,separation_comm,add_comm]
        simp only [edges,f,Stew.tag,image_insert,image_singleton]; rfl
    have hF : (∑ i: Lat.Row c × Lat.Row c,F (f i)) ≤ Fintype.card (Site c)*A:=by
        refine le_trans ?_ hv; unfold band; have hr:Injective f:=by
              rintro ⟨i,j⟩ ⟨x,y⟩ h; obtain ⟨ht,hq⟩:= (tagged ..).1 h; exact Prod.ext (Prod.ext_iff.mp ht).1 (Prod.ext_iff.mp hq).1 -- fails
        rw [← sum_image hr.injOn]; exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _=> grains locationP _ ht _
    let Y i:= t^2 * Gan id id m p i; have hh:(∑ i,Y i) ≤ C*(Fintype.card (Site c)*A):=by
         apply le_trans _ (mul_le_mul_of_nonneg_left hF (zero_le_one.trans hC)); rw [Fintype.sum_prod_type]; simp_rw [he]; unfold Lat.Row; simp_rw [Fintype.sum_prod_type (α₁:=Site c) (α₂:=Lat.Fiber)]
         rw [Finset.mul_sum]; apply sum_le_sum; intro v _; unfold Y Gan; rw [Finset.mul_sum, sum_comm (s:= (univ:Finset Lat.Fiber)), mul_sum]; apply sum_le_sum; intro j _; -- fix comm
         let z:=costS m v j; simp_rw [← Finset.sum_mul]; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (H (V v j)) (show 0≤ z from cost_nn ..)) (sq_nonneg t)).trans; change t^2*(z*(C*∑ x,∑ y,‖p (v,x) (j,y)‖))≤ C*(_*t^2*z); exact le_of_eq (by ring)
    rw [show (∑ x,Y x)=(Fintype.card (Site c):ℝ)* Y i from ?_] at hh
    · have hr:0 < (Fintype.card (Site c):ℝ):=by positivity
      change Gan id id m p i ≤ t⁻¹^2*C*A; rw [inv_pow, mul_assoc, inv_mul_eq_div, le_div_iff₀ (sq_pos_of_pos ht), mul_comm]
      apply le_of_mul_le_mul_left _ hr; exact hh.trans_eq (by ring)
    have he' j': Y j'=Y i := by unfold Y; rw [Tempo.uniform (X:=p) hQ j' i]
    simp_rw [he']; simp
end YM.QCD.Globe
