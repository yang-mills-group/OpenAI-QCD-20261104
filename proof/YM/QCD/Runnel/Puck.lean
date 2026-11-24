import YM.QCD.Runnel.Divide

/-!
# Buy a near block with true supports. Used with single-ball tiling on fixed chunks.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.QCD.Run
open Lat Lattice Gauge Wilson Cost Function Finset Kit
open scoped Matrix Matrix.Norms.L2Operator BigOperators
variable {f : Side} {D E : Type*} [DecidableEq D] [DecidableEq E] [Fintype D] [Fintype E]
variable {x : D→Site f} {y : E→Site f} {δ b R : ℝ} {B m : ℕ} {M : Grid f→ArrayL D E}

def circulant (x : D→Site f) (k : Lat.Frame f) := rides (Equiv.refl D) fun i=> touch (colour (k (x i)))
lemma gyro {X : ArrayL D E} (x : D→Site f) (y : E→Site f) (i j) (k : Lat.Frame f): cell (circulant x k*X*star (circulant y k)) i j = touch (colour (k (x i)))*cell X i j*star (touch (colour (k (y j)))):=by
  have he (j): cell (circulant x k*X) i j=touch (colour (k (x i)))*cell X i j:=by
    rw [cell_mul,sum_eq_single i]
    · congr 1; ext a b; simp [cell,circulant,rr]
    · intro v _ hv; rw [show cell (circulant x k) i v=0 from ?_,zero_mul]; ext a r; simp [cell,circulant,rr,Ne.symm hv]
    simp
  rw [cell_mul, sum_eq_single j]
  · rw [he]; congr 1; ext a r; rw [circulant,ride_ad]; simp [cell,rr]
  · intro v _ hv; rw [show cell (star (circulant y k)) v j=0 from ?_,mul_zero]; ext a r; rw [circulant,ride_ad]; simp [cell,rr,hv]
  simp
lemma gyro_id (k : Lat.Frame f): circulant id k=siteRot k:=rfl

-- block cost is one
def needle (i : D): Matrix Fiber (D×Fiber) ℂ:=Matrix.of fun a j=> if (i,a)=j then 1 else 0
lemma needles (i : D):‖needle i‖=1:=by
  have he : needle i*(needle i)ᴴ=1:=by ext x y; by_cases h:x=y <;> simp [needle,Matrix.mul_apply,ite_mul,h,Matrix.one_apply]
  have hh:= Matrix.l2_opNorm_conjTranspose_mul_self (needle i)ᴴ; rw [Matrix.conjTranspose_conjTranspose,he,oneNorm,Matrix.l2_opNorm_conjTranspose] at hh; nlinarith [norm_nonneg (needle i)]
lemma cell_pay (i j) (D : ArrayL D E):‖cell D i j‖ ≤ ‖D‖:=by
  rw [show cell D i j=needle i*D*(needle j)ᴴ from ?_]; apply (Matrix.l2_opNorm_mul _ _).trans; rw [Matrix.l2_opNorm_conjTranspose,needles,mul_one]; exact (Matrix.l2_opNorm_mul (needle i) D).trans (by rw [needles,one_mul])
  ext p q; simp [cell,needle,Matrix.mul_apply,ite_mul,mul_ite,apply_ite]

def cellC (i:D) (j:E): ArrayL D E→L[ℂ] Bundle := LinearMap.toContinuousLinearMap { toFun:=fun Z=> cell Z i j,map_smul':=fun _ _=>rfl,map_add':=fun _ _=>rfl }
def Pile (b : ℝ) (m : ℕ):= (↑((m+m+1)^4:ℕ):ℝ)* Real.exp b -- check binder m*? lean elaborates Real multiplication first.
lemma pile_pos (b : ℝ) (m : ℕ):0<Pile b m:=by unfold Pile; positivity
lemma count_bill (j : Site f) (hp : Injective x) : ((univ.filter (fun i=>separation (x i) j≤m)).card:ℝ) ≤ (m+m+1 : ℝ)^4:=by
  let U := univ.filter (fun i=>separation (x i) j≤m)
  have ht:= Corona.halo_size ({j}:Support f) m
  rw [card_singleton,one_mul] at ht
  have he : U.card ≤ (m+m+1)^4:=le_trans ?_ ht
  · exact_mod_cast he
  apply card_le_card_of_injOn x _ hp.injOn
  intro i hi; apply halo_spec.mpr; refine ⟨_, mem_singleton_self _,?_⟩; rw [separation_comm]; exact (mem_filter.mp hi).2

lemma rents {p : Site f} (hb : 0≤b) (hp : m≤B): rent b B (halo m {p})≤Real.exp b:=by
  have he : Corona.Ships {p} (B+B+1):=by intro i hi j hj; simp only [mem_singleton] at hi hj; rw [hi,hj]
  have hh := Corona.list_cost B (D:={p}) (X:=halo m {p}) ⟨Corona.halo_mono hp (Subset.refl _),Corona.ship_halo _ he⟩
  unfold rent; rw [card_singleton] at hh; exact Real.exp_le_exp.mpr (mul_le_of_le_one_right hb (by exact_mod_cast hh))
lemma tiled (hX : Injective x) (hY : Injective y) (hb : 0≤b) (hp : m≤B) (hr : 0≤R)
    (W : Pulse f→ArrayL D E) (hU : ∀ U, W (settled U)=M U)
    (h : Reads (x∘Prod.fst) (y∘Prod.fst) m M)
    (hg : ∀ U k, M (gauge k U)=circulant x k*M U*star (circulant y k))
    (hw : ∀ U∈Kingdom f δ,DifferentiableAt ℂ W U)
    (hv : ∀ U∈Kingdom f δ, ‖W U‖≤R): Heritage x y δ b B M (Pile b m*R):=by
  let S (i:D):= halo m {x i}
  let X (i:D) (j:E) := if separation (x i) (y j) ≤ m then fun Z=> cell (W Z) i j else 0
  let c (i:D) (j:E):= if separation (x i) (y j)≤m then R else 0
  have he (i:D) : (S i : Set (Site f))=view (x i) m:=by ext; simp [view,S,halo_spec]
  refine Heritage.spanning (fun i _=> S i) X c ?_ ?_ ?_ ?_
  · intro i j; unfold X c; split_ifs with hh
    · refine ⟨hr,fun _=> ⟨(halo_subset m _ (mem_singleton_self _)), halo_spec.mpr ⟨_,mem_singleton_self _,hh⟩⟩,fun Z hZ=> (cellC i j).differentiableAt.comp Z (hw Z hZ),fun Z hZ=> (cell_pay ..).trans (hv Z hZ),?_,fun U k=>by simp only [hU]; rw [hg]; exact gyro ..⟩ -- fix hv
      rw [he]; intro U V H; ext a r; dsimp only [comp_apply]; rw [hU,hU]; exact h.sees (i,a) (j,r) U V H
    exact Crop.zero
  · intro i j U; unfold X; split_ifs with hh; · simp only [hU]
    ext a r; exact (h.absent (i,a) (j,r) hh U).symm
  · intro i
    have hl : ((univ.filter (fun j=>separation (x i) (y j)≤m)).card:ℝ)≤ (m+m+1 : ℝ)^4:=by simpa only [separation_comm (x i)] using! (count_bill (m:=m) (x i) hY)
    have hq : ∑ j:E,rent b B (S i)*c i j= ((univ.filter (fun j=>separation (x i) (y j)≤m)).card:ℝ)*(rent b B (S i)*R):=by simp [c,mul_ite,← sum_filter]
    rw [hq]; refine (mul_le_mul hl (mul_le_mul_of_nonneg_right (rents hb hp) hr) (mul_nonneg (fair ..).le hr) (by positivity)).trans (le_of_eq ?_); unfold Pile; push_cast; rw [mul_assoc]
  intro j
  simp only [c,mul_ite,mul_zero,← sum_filter]; apply (sum_le_sum (fun i _=> mul_le_mul_of_nonneg_right (rents hb hp) hr)).trans; rw [sum_const,nsmul_eq_mul]
  refine (mul_le_mul_of_nonneg_right (count_bill _ hX) (mul_nonneg (Real.exp_pos _).le hr)).trans (le_of_eq ?_); unfold Pile; push_cast; rw [mul_assoc]
end YM.QCD.Run
