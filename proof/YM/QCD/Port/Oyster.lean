import YM.QCD.Port.Cove
import YM.Extra.ITERATION_NO_LOSS.Transport
/-! # unmasked atom toll, use no saturation here -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port.AtomF
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra Iteration Rudder
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {c f:Side}{v η A t δ σ :ℝ}{B b k:ℕ}
-- support pricing by Atom footprint length and expo
lemma leaf_cash (s: ℝ)(hs:0<s): ∃ C δ:ℝ,0<C∧0<δ ∧ ∀ (n:Side)(W:Slot)(x:Site n)(z:Pulse n)(h:z∈Kingdom n δ)(i:su.ColorIndex), ‖leafC W x z i‖ ≤ C*Real.exp (s*W.length):=by
 choose K hK using string_lin
 let C:ℝ:=∑ i : su.ColorIndex, ‖K i‖
 let δ:=Real.exp (s/2)-1
 have hc:0≤C:=by unfold C; positivity
 refine ⟨2*C+1,δ,by positivity,sub_pos.mpr (Real.one_lt_exp_iff.mpr (by positivity)),fun n W x z h i=>?_⟩
 obtain ⟨U,hU⟩:=Set.mem_iUnion.mp h
 rw [Metric.mem_ball,dist_eq_norm] at hU
 let v:=Real.exp (s*W.length)
 have he j w(hw:List.length w≤2*W.length):‖pursueP z j w‖ ≤ v:=by
   apply (pose z U w j hU.le).trans; apply (pow_le_pow_right₀ (show 1 ≤ 1+δ from le_add_of_nonneg_right ((norm_nonneg _).trans hU.le)) hw).trans; unfold δ v; rw [add_sub_cancel,← Real.exp_nat_mul]; push_cast; ring_nf; rfl
 have hv:0<v:= Real.exp_pos _
 unfold leafC; rw [← hK]; apply ((K i).le_opNorm _).trans; rw [norm_smul]; apply le_trans (mul_le_mul (show ‖K i‖ ≤ C from single_le_sum (f:=fun i=> ‖K i‖) (fun j _=>norm_nonneg (K j)) (mem_univ i)) ((mul_le_of_le_one_left (norm_nonneg _) (by norm_num)).trans ((norm_sub_le ..).trans (add_le_add (he _ _ (length_max W)) (he _ _ (by simpa only [Lattice.reverse,List.length_map,List.length_reverse] using length_max W))))) (by positivity) hc); change C*(v+v)≤(2*C+1)*v; nlinarith

def hatch (W: Atom su k)(p: Strut f)(x : Site f) (P:Pulse f):ℂ:=∑ i,(W.coeff i:ℂ)*∏ j,leafC (W.leg j) ((act p).symm x) (swing p P) (i j)
lemma settledP (W: Atom su k)(p:Strut f)(x: Site f)(U:Grid f): hatch W p x (settled U)=(W.unmasked (sky p U) ((act p).symm x):ℂ):=by simp only [hatch,still,pinning,Atom.unmasked,Atom.poly,Complex.ofReal_sum,Complex.ofReal_prod,Complex.ofReal_mul]
lemma hatchet (W:Atom su k)(p:Strut f)(x:Site f):Differentiable ℂ (hatch W p x):=by
 unfold hatch; refine Differentiable.fun_sum fun i _=>Differentiable.const_mul ?_ _
 have hg (S: Finset (Fin k)):Differentiable ℂ (fun P=>∏ j∈S,leafC (W.leg j) ((act p).symm x) (swing p P) (i j)):=by
    induction S using Finset.induction_on with
    | empty=>simp only [prod_empty]; exact differentiable_const _
    | insert a l hl ih=> simp_rw [prod_insert hl]; exact ((growing (W.leg a) ((act p).symm x) (i a)).comp (bendD p)).mul ih
 exact hg univ

def mature (W:Atom su k)(p:Strut f)(x: Site f):= (W.footprint ((act p).symm x)).image (act p)
lemma tag_cost (W:Atom su k)(p:Strut f)(x:Site f)(hb:0≤v)(ht:0<B)(hy:v/B≤σ):rent v B (mature W p x)≤Real.exp (v*(1+2*(k:ℝ))+σ*W.length):=by
  unfold Run.rent mature; rw [cover_map (act p) (Push.Local.turn_sep p.1 p.2)]; exact (LeafM.house (Rudder.Bloom.mk [] W.leg 0) _ ht hb hy)
lemma ticketM (W:Atom su k)(p:Strut f)(x:Site f): LocalOn (mature W p x) ((hatch W p x) ∘ settled):=by
  intro U V H; simp only [comp_apply, settledP]; apply congr_arg Complex.ofReal
  let z:=(act p).symm x
  change W.unmasked (sky p U) z=W.unmasked (sky p V) z; unfold Atom.unmasked
  have he:Agrees (W.footprint z) (sky p U) (sky p V):=agrees_pull _ _ H
  apply congr_arg W.poly
  funext i
  refine LocalOn.expandAt _ _ ((W.leg i).covered (G:=su)) z (sky p U) (sky p V) (agrees_mono he ?_)
  rintro _ ⟨y,hy,rfl⟩; exact mem_image_of_mem _ (mem_insert_of_mem (mem_biUnion.mpr ⟨i,mem_univ _,hy⟩))
lemma publicK (W:Atom su k)(hw:W.Invariant)(p:Strut f) (x:Site f)(U: Grid f)(q: Frame f): hatch W p x (settled (gauge q U))=hatch W p x (settled U):=by
 simp only [settledP,sky,pull_gauge]; apply congr_arg Complex.ofReal
 unfold Atom.unmasked; simp_rw [Rudder.Bloom.slotRot]; apply hw

def field (F:Site f→ℂ):Sheet f:= rides (Equiv.refl _) fun x=> F x • 1
def frostW (W:Atom su k)(p:Strut f) (U:Grid f): Sheet f:= field fun x=>hatch W p x (settled U)
lemma armor (hs:0<σ)(v:ℝ)(hv:0≤v)(k:ℕ): ∃ C δ:ℝ,0<C∧0<δ∧ ∃ M:ℕ,∀ B:ℕ, M ≤B→∀ (f:Side)(W:Atom su k)(p:Strut f),W.Invariant→ Own f δ v B (frostW W p) (C*W.budget σ):=by
  let s:=σ/2; have he:=half_pos hs
  obtain ⟨C,δ,hc,hδ,h⟩:=leaf_cash s he
  obtain ⟨l,hl⟩:=exists_nat_gt (v/s)
  let T:=C^k*Real.exp (v*(1+2*(k:ℝ))); have hT:0<T:=by unfold T; positivity
  refine ⟨T,δ,hT,hδ,l+1,fun B hB f W p hp=>?_⟩
  let Y:=mature W p; let H x P:= hatch W p x P • (1:Bundle)
  let u:=C^k* W.budget s
  let Q (x y:Site f) :Pulse f→ Bundle:= if x=y then H x else 0
  have ht:0≤u:= by unfold u Atom.budget Atom.magnitude; positivity
  have hh : 0<B :=by omega
  have hm : v/B ≤ s:=by
     have hi:(l:ℝ)≤ B:=by exact_mod_cast (show l≤B by omega)
     rw [div_le_iff₀ (by exact_mod_cast hh)]; rw [mul_comm]; exact (div_le_iff₀ he).1 (hl.le.trans hi)
  have hq x: rent v B (Y x)*u ≤ T*W.budget σ:=by apply (mul_le_mul_of_nonneg_right (tag_cost W p x hv hh hm) ht).trans_eq; unfold u T Atom.budget; rw [Real.exp_add,show σ*↑W.length=s*W.length+s*W.length from by unfold s; ring, Real.exp_add]; ring
  refine Heritage.spanning (fun i _=> Y i) Q (fun x y=> if x=y then u else 0) (fun i j=> ?_) (fun i j=>?_) (fun x=> ?_) (fun j=> ?_)
  · unfold Q; split
    next h' => subst j; change Crop i i δ (Y i) (H i) u
               refine ⟨ht,fun _=>?_,fun _ _=> ((hatchet W p i).smul_const _ _),fun Z hZ=>?_,fun U V h=> congr_arg (· • (1:Bundle)) (ticketM W p i U V h),fun U q=>?_⟩ -- syntax
               · have hx : i∈Y i:= mem_image.mpr ⟨_,mem_image.mpr ⟨0,mem_insert_self ..,show wrap f 0+(act p).symm i= (act p).symm i by simp⟩,(act p).apply_symm_apply _⟩; exact ⟨hx,hx⟩
               · unfold H hatch u; rw [norm_smul,oneNorm,mul_one]; unfold Atom.budget Atom.magnitude; rw [sum_mul,mul_sum]; refine (norm_sum_le ..).trans (sum_le_sum fun j _=>?_); rw [norm_mul,norm_prod,Complex.norm_real,Real.norm_eq_abs,mul_left_comm (C^k) _] -- wrong
                 have he (j':Fin k):= h f (W.leg j') ((act p).symm i) _ (stasis p Z hZ) (j j')
                 exact mul_le_mul_of_nonneg_left ((prod_le_prod (s:=univ) (fun j _=>norm_nonneg _) (fun y _=> he y)).trans_eq (by unfold Atom.length; push_cast; rw [mul_sum,Real.exp_sum]; simp [prod_mul_distrib])) (abs_nonneg _)
               unfold H; rw [publicK W hp p]; have hi:=touch_u (x:=colour (q i)) ⟨su.mat_star_mul _,su.mat_mul_star _⟩; simp only [Matrix.mul_smul,Matrix.smul_mul,mul_one,hi.2] --
    next h => exact Crop.zero
  · intro x; unfold Q frostW field; split_ifs with hh
    · subst j; ext a b; exact (if_pos rfl).symm
    ext a b; exact (if_neg (show ¬ i=j from hh)).symm
  · simpa [mul_ite] using (hq x)
  simpa [mul_ite] using hq j
end YM.QCD.Port.AtomF
