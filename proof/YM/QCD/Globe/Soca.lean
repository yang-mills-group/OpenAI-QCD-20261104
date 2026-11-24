import YM.QCD.Globe.Ursa
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
variable (S h) {a b t w κ x:ℝ}{J_l:ℕ}
set_option quotPrecheck false
open Brick Nola
local notation "g"=> sliceL S h
lemma recolor (D: Sheet f)(hp: Cost.Chiral (chirality f) D): (tied S h 0 1)* D⁻¹= railDay (D⁻¹*(tied S h 0 1)ᴴ):=by
  let X:= D; let Y:=chirality f; let Q:=conn S h; let Z:=chirality c
  change Q*X⁻¹=Z*((X⁻¹*Qᴴ)ᴴ)*Y
  have hx : star X=Y*X*Y:=hp
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose,show star X⁻¹=(star X)⁻¹ from (Matrix.conjTranspose_nonsing_inv _),hx, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  have hy : Y⁻¹=Y:= Matrix.inv_eq_left_inv chi_sq
  have hz : Z*Q=Q*Y:= (tiedSpin S h 0 1 _).symm -- defeq Q
  rw [hy]; simp only [← Matrix.mul_assoc]; rw [hz, Matrix.mul_assoc Q Y Y,show Y*Y=1 from chi_sq, Matrix.mul_one,Matrix.mul_assoc _ Y Y, show Y*Y=1 from chi_sq, Matrix.mul_one]
lemma rodpay (N:ℕ)(X:Kit.Rail f c)(hi:Cent (g).parent id m a X)(i:Keys f N): ∑ j:Keys c N, ‖powerF X i j‖*rodM ((g).parent (locationP i)) (locationP j) m ≤ stemF N*a:=by
    let p:= locationP i; let A(v:Site c):= costS m ((g).parent p) v*‖cell X p v‖
    apply le_trans (b:= ∑ j: Keys c N,A (locationP j)) (sum_le_sum (fun j _=> ?_)); · rw [crystals A]; exact mul_le_mul_of_nonneg_left (hi _) (by unfold stemF Jets.Sun.fingers; positivity)
    rw [rodM,bloomP] -- rodM def mismatch
    rw [mul_comm]; exact mul_le_mul_of_nonneg_left (Brick.duty ..) (cost_nn ..)
lemma sizeP (M: Finset (Keys f N)):Nola.tell (edges ((g).parent∘locationP) M) m≤2^m*Nola.tell (edges locationP M) m:=by
    let F:= edges locationP M
    have he: reel (edges ((g).parent∘locationP) M) ≤ 1+reel F:=by
         apply roof; intro i hi j hj; obtain ⟨x,hx,rfl⟩:= mem_image.mp hi; obtain ⟨y,hy,rfl⟩:= mem_image.mp hj; let X:=locationP x; let Y:=locationP y
         have hp:= shorter (m:=1) (sliceL S h) X Y -- too weak, actually need +1; adapt
         have hg:= Corona.foreshorten (sliceL S h) X Y; let r:=g; let K:= reel F
         have hh:separation X Y ≤ K:= roofS (Finset.mem_image_of_mem _ hx) (Finset.mem_image_of_mem _ hy)
         apply Nat.le_of_mul_le_mul_left _ (r.count.property);
         rw [Nat.mul_add,Nat.mul_one, Nat.add_comm]; apply hg.trans; apply Nat.add_le_add_right _; exact hh.trans (Nat.le_mul_of_pos_left _ r.count.property)
    unfold Nola.tell; rw [← mul_pow]; apply pow_le_pow_left₀ (by positivity); have h:(↑(reel (edges ((g).parent∘locationP) M)):ℝ)≤↑(1+reel F:ℕ):=Nat.cast_le.mpr he; push_cast at h; change _ ≤ (2*(↑(reel F)+ (1:ℝ))); linarith [Nat.cast_nonneg (α:=ℝ) (reel F)] -- possibly roof ambiguous
lemma emerges (P:Plan j)(X:EvenA f N)(R:Sheet f)(hp: Tempo R)(hz: GrassA X t m κ)(hf: Cent (g).parent id m a ((father S h+R)⁻¹*(tied S h 0 1)ᴴ))(ht:0 < x)(hx:0<t)(hv: (stemF N*a)*x≤ t*w)(hw: 0 ≤ w)(hy:w≤1)(ha:0≤a)(hj:∀ i:Finset (Keys f N),i.card<J_l→coef i X.val=0) : GrassA (warp S h R X) x m ((S.L.val:ℝ)^4*w^(J_l)*2^m*κ):=by
     let Z:=father S h+R
     let A:=tied S h 0 1
     have hZ: Cost.Chiral (chirality f) Z:=by unfold Z; have h:= ticketStar P S h 0 1; rw [tree_zero] at h; have he:Cost.Chiral (chirality f) R:=(Orbit.funds0 R).mp hp.song; unfold Cost.Chiral; rw [star_add,h,he, Matrix.mul_add,Matrix.add_mul] -- tree_zero
     have h1:=recolor S h Z hZ; have hX: (warp S h R X).val=changeVars (powerF (Z⁻¹*Aᴴ)) X.val:=by unfold warp; rw [h1]; rfl
     unfold GrassA; rw [hX]; have he:= Nola.cargoX locationP locationP (powerF (Z⁻¹*Aᴴ)) X.val ht hx hw (show 0 ≤ (2:ℝ)^m by positivity) (show 0≤ stemF N*a from mul_nonneg (by unfold stemF Jets.Sun.fingers; positivity) ha) hv hy (show ∀ y,∑ j,‖powerF (Z⁻¹*Aᴴ) y j‖*rodM (((g).parent∘locationP) y) (locationP j) m ≤ _ from rodpay S h N _ hf) (sizeP S h) hj
     apply he.trans ((mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ w^J_l*2^m)).trans _); rw [site_card,site_card,h]; push_cast; exact le_of_eq (by ring)
end YM.QCD.Globe
