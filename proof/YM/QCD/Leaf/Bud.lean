import YM.QCD.Leaf.Seed

/-! # Leaf analytic bundles in fine count, arbitrarily paid cover exponent
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.LeafM
open Run Kit Lat Function Finset Lattice RG Rudder Filter Matrix Metric Classical Paths
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator InnerProductSpace
variable {n : Side}{I : Type}{k B m : ℕ}(W: Bloom k)(x:Site n){b r t δ ξ p σ A:ℝ}
abbrev twig (W: Bloom k): Atom su k:=⟨W.petals,0⟩
def transient (ξ:ℝ)(P:Pulse n):Bundle:=∑ i,(∏ j,leafSat (W.petals j) x ξ P (i j)) • W.coeff i
def satin (ξ:ℝ)(U: Grid n):Bundle:=W.hues fun i=>pulp (W.petals i) x ξ U
def yard (ξ:ℝ)(U:Grid n):Sheet n:=rides (Equiv.refl _) fun x=> satin W x ξ U
lemma satin_eq (U:Grid n):transient W x ξ (settled U)=satin W x ξ U:=by simp only [transient,satin,Bloom.hues,connecting,Complex.ofReal_prod]
open YM.Next.Scheduling.Wages
lemma locateP (j:Fin k): walkCuts (W.petals j) x⊆(twig W).footprint x:=by
  unfold walkCuts Atom.footprint; apply image_subset_image; intro i hi; exact mem_insert_of_mem (mem_biUnion.mpr ⟨j,mem_univ _,hi⟩)
lemma usesS : LocalOn ((twig W).footprint x) (satin W x ξ):= by
  intro U V H; exact congr_arg W.hues (funext (fun i=> uses (W.petals i) x U V (agrees_mono H (fun _ hk=>locateP W x i hk)) ξ))

lemma house (hB:1≤B)(hb:0≤b)(hg:b/B≤r) : rent b B ((twig W).footprint x) ≤ Real.exp (b*(1+2*(k:ℝ))+r*(twig W).length):=by
  unfold rent; apply Real.exp_le_exp.mpr; let Y:=(twig W).footprint x
  have hp:B*coverNumber B ((twig W).footprint x) ≤ _:=traversed (twig W) x B hB
  let l := (twig W).length
  have hv: (B:ℝ)*coverNumber B Y ≤ B + ( (k:ℝ)*(2*(B:ℝ))+l):=by exact_mod_cast hp
  have hy:0<(B:ℝ):=by exact_mod_cast hB
  have hk:(coverNumber B Y:ℝ) ≤ (1+2*k)+ l/(B:ℝ):=by field_simp; linarith
  nlinarith only [mul_le_mul_of_nonneg_left hk hb,mul_le_mul_of_nonneg_right hg (Nat.cast_nonneg (α:=ℝ) l), show b*((l:ℝ)/(B:ℝ))=(b/B)*l by ring]
structure Bottle (t v δ ξ:ℝ):Prop where
  pours (n:Side)(W: Slot)(x:Site n)(P:Pulse n)(hp:P∈ Kingdom n (δ*ξ^2))(i : su.ColorIndex) :
      DifferentiableAt ℂ (fun y=>leafSat W x ξ y i) P ∧ ‖leafSat W x ξ P i‖ ≤ v*ξ*Real.exp (t*W.length)
def cal (W: Bloom k) (v ξ t:ℝ):ℝ:= W.price*((v*ξ)^k*Real.exp (t*(twig W).length))
lemma caliber (hv:0≤p)(hξ:0 ≤ ξ): 0≤ cal W p ξ t:=by unfold cal; exact mul_nonneg W.price_nn (by positivity)
lemma trills (h : Bottle t p δ ξ)(hp:0≤p)(hξ:0≤ξ)(hh: W.Spins): Crop x x (δ*ξ^2) ((twig W).footprint x) (transient W x ξ) (cal W p ξ t):=by
  refine ⟨caliber W hp hξ, fun _=>?_,fun Z hz=> ?_,fun Z hz=>?_,?_,?_⟩
  · have he : x∈(twig W).footprint x := Finset.mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩; exact ⟨he,he⟩
  · unfold transient; apply DifferentiableAt.fun_sum; intro i hi; have hh (S: Finset (Fin k)):DifferentiableAt ℂ (fun a=> ∏ j∈S, leafSat (W.petals j) x ξ a (i j)) Z:=by
       induction S using Finset.induction_on with
       | empty=> simp only [prod_empty]; exact differentiableAt_const _
       | insert j S hj ih=>simp_rw [prod_insert hj]; exact ((h.pours n _ x Z hz (i j)).1).mul ih
    exact (hh univ).smul_const _
  · unfold transient cal Bloom.price; apply (norm_sum_le ..).trans; rw [sum_mul]; refine sum_le_sum fun i _=>?_ ; rw [norm_smul,norm_prod,mul_comm]; apply mul_le_mul_of_nonneg_left _ (norm_nonneg _); apply (prod_le_prod (fun _ _=> norm_nonneg _) (fun j _=> (h.pours n _ x Z hz (i j)).2)).trans; unfold Atom.length; push_cast; simp [prod_mul_distrib,mul_sum,Real.exp_sum,twig]
  · intro U V hv; rw [Function.comp_apply,Function.comp_apply,satin_eq,satin_eq]; exact usesS W x U V hv
  intro U g; rw [satin_eq,satin_eq]; unfold satin; simp_rw [gaugeP]; rw [hh]

def pricey (v ξ b t:ℝ):= Real.exp (b*(1+2*(k:ℝ)))*W.price*(v*ξ)^k*Real.exp (2*t*(twig W).length)
lemma yardage (h: Bottle t p δ ξ)(ht:b/B ≤ t)(hp:0≤p)(hb:0≤b)(hr:0≤ξ)(hB:0<B)(he:W.Spins): Own n (δ*ξ^2) b B (yard (n:=n) W ξ) (pricey W p ξ b t):=by
  let U (x y:Site n) := (twig W).footprint x
  let V (x y:Site n):Pulse n→Bundle:= if x=y then transient W x ξ else 0
  let Z (x y:Site n):ℝ:= if x=y then cal W p ξ t else 0
  have hi (i:Site n): rent b B (U i i)*cal W p ξ t≤pricey W p ξ b t:= by
    apply le_trans (mul_le_mul_of_nonneg_right (house W i hB hb ht) (caliber W hp hr)); rw [cal,pricey, Real.exp_add]; rw [show 2*t*↑(twig W).length=t*(twig W).length+t*(twig W).length by ring,Real.exp_add]; exact le_of_eq (by ring)
  refine Heritage.spanning U V Z (fun i j=>?_) (fun i j S=>?_) (fun i=> ?_) (fun j=>?_)
  · unfold V Z; split_ifs with h'
    · subst j; exact trills W i h hp hr he
    exact Crop.zero
  · unfold V; split_ifs with h'
    · subst j; rw [satin_eq]; ext a r; simp [yard,rr,Run.cell]
    ext a r; simp [yard,rr,h',Run.cell]
  · simpa only [Z,mul_ite,mul_zero,Fintype.sum_ite_eq] using hi i
  simpa only [Z,mul_ite,mul_zero,Fintype.sum_ite_eq'] using hi j

def trackP (W: Bloom k)(u:ℝ)(n:Side)(V:Grid n):Sheet n := yard W u V*routeM 0 V W.tail
lemma postM (k:ℕ)(hr:0<σ)(ht:0≤b): ∃ δ C :ℝ,∃ m:ℕ, 0 < δ ∧ 0<C ∧∀ B:ℕ,m≤B→∀ (ξ:ℝ),0<ξ→ξ≤1→∀ (n:Side)(W: Bloom k), W.Spins → Own n (δ*ξ^2) b B (trackP W ξ n) (C*(W.paid σ)*ξ^k):=by
  let s:=σ/2; have hx:=half_pos hr
  obtain ⟨c,δ,hp,hD,hA⟩:= file s hx
  have hc:=zero_lt_one.trans_le hp
  obtain ⟨m,d,hy,hB,H⟩:= ballad b hr
  obtain ⟨M,hM⟩:=exists_nat_gt (b/s)
  let w:=min δ d
  refine ⟨w,Real.exp (b*(1+2*(k:ℝ)))*c^k*Real.exp (σ*m),max (2*m) M,lt_min hD hB,by positivity,fun B hz ξ h hh n W hZ=>?_⟩
  have he:= (le_max_left ..).trans hz
  have hE:0<B:=by omega
  have hF: b/B≤s:=by
    have hu:0 < (B:ℝ):=by exact_mod_cast hE
    have hd:(M:ℝ) ≤ B:=by exact_mod_cast (le_max_right ..).trans hz
    apply (div_le_iff₀ hu).2; have h: b/s ≤ B :=hM.le.trans hd; have hh:= (div_le_iff₀ hx).1 h; unfold s; linarith
  have hv:Bottle s c δ ξ:= ⟨fun n W x Y hv i=> hA ξ h hh n W x Y i hv⟩
  have hg:= yardage (n:=n) W hv hF hc.le ht h.le hE hZ; have hi:=W.price_nn
  apply ((hg.clip (mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity))).meet ((rides_for (f:=n) 0 W.tail ht hB hr hy he H).clip (show w*ξ^2≤d from (mul_le_of_le_one_right (lt_min hD hB|>.le) (pow_le_one₀ h.le hh)).trans (min_le_right ..))) (mul_pos (lt_min hD hB) (by positivity)) ht (by unfold pricey; positivity) (by positivity)).mono
  unfold pricey Bloom.paid; rw [Bloom.span,Nat.cast_add,Nat.cast_sum,mul_add,Real.exp_add]; unfold s Atom.length; push_cast; rw [mul_pow]; apply le_of_eq; rw [show 2*(σ/2)=σ by ring]; rw [mul_add σ,Real.exp_add]; ac_rfl
end YM.QCD.Leaf.LeafM
