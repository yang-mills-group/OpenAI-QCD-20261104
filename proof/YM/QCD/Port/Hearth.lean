import YM.QCD.Port.Gaze
/-! # Hit reserve for bright vs long. combine after. `tiny` buys affinely for Good halo only.
-/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF Push.AbsoluteSums Footprint Trees
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {f c:Side}{F:ℕ}{u v η ξ t p C D A R z q w Ω π κ:ℝ}{b B i:ℕ}{j k:ℕ}{L:Flight j k}{J:Plan k}{H:f.val=c.val*L.L.val}{X:St f}{W:ℕ→Atom su 2}
local notation "Mx"=> Modes c F
local notation "S"=> sliceL L H
variable (P : Swathe L H X W J u v η p q b)
lemma options (v : Site f)(x:XMark f) : x=none ∨ ∃ i : Support f,x=some i:= by cases x <;> simp
-- insert anchor harmless.
lemma cash_l {I J:Type*}[Fintype I][Fintype J]{U:Grid f→ArrayL I J}{pI:I→Site f}{pJ:J→Site f}{X:Land f I J}{Y:Pays f I J}(h:Pack pI pJ v η b U A X Y)(i j x B)(hh:x=pI i∨x=pJ j)(ht: π≤η): (∑ z:Support f, crease x B Y i j (some z)*Run.rent π b (punch x B (some z)))≤ Real.exp (-(η-π)*fossil B b)* duel Y i j η b:=by
  trans ∑ z∈satZip x B, Run.rent π b z*Y i j z
  · refine le_of_eq ?_; rw [← sum_subset (subset_univ (satZip x B)) (fun a _ ha=>by simp [crease,ha])]; apply sum_congr rfl; intro z hz; unfold crease punch; simp only [hz,if_true]; by_cases he : Y i j z=0; · rw [he,zero_mul,mul_zero]
    rw [insert_eq_of_mem (hh.elim (fun H=> H ▸ ((h.crop i j z).2.1 he).1) (fun H=> H ▸ ((h.crop i j z).2.1 he).2)), mul_comm]
  exact worthZ h i j x π B hh ht
lemma one_more (x:Site f) (B:ℕ) (ht:0≤π): Run.rent π B (punch x B none)≤ Real.exp π:=by
  have hv: coverNumber B (punch x B none) ≤ 1:= by
    refine le_trans (b:=({x}: Support f).card) (Nat.find_min' _ ⟨_,show covers B (punch x B none) {x} from ⟨fun a ha=> ha,Corona.ship_halo _ (fun i hi j hj=> by rw [mem_singleton.mp hi,mem_singleton.mp hj])⟩,rfl⟩) ?_ -- `b` syntax fix
    simp
  exact Real.exp_monotone ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hv) ht).trans_eq (by norm_num))

def loftCost (p q:ℝ)(F b B:ℕ)(t η a:ℝ):ℝ:=(F*AtomF.rays*2+0)*(Real.exp (-(η-a)*fossil B b)*q)+ t^2*fingers F^2*(2*(Real.exp (-(η-a)*fossil B b)*p))

def shells (P:Swathe L H X W J u v η p q b)(F B:ℕ)(t :ℝ) (Z:ℝ) (x: Varn f c): ℝ:= if waxV x=none then Z else level P F B t x
lemma pax {i:Site c}(he : 0≤π)(h:b≤B)(hv:0<v)(ht:0<t) (x:Varn f c): level P F B t x * Run.rent π B (payT S B x) ≤ level P F B t x * Run.rent π b (payT S B x):=by
  apply mul_le_mul_of_nonneg_left _ (grew P x hv ht); exact Real.exp_monotone (mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (YM.Next.Scheduling.cover_earns h _)) he)
lemma sky_hits (F B:ℕ)(hp:π≤η)(hb:b≤B)(he:0≤π)(hz:0≤z)(hv:0<v)(ht:0<t):
 Anchored (orbitM S) (shells P F B t z) (fun i=>coverNumber B (payT S B i)) π (2*z*Real.exp π+loftCost p q F b B t η π):=by
   intro i; let E:= Real.exp (-(η-π)*fossil B b)
   let T x:=shells P F B t z x*Run.rent π B (payT S B x); let W x:=level P F B t x
   let Z x:= if orbitM S x=i then T x else 0
   have ht' x:0≤T x:=mul_nonneg (by unfold shells; split; exact hz; exact grew P x hv ht) (Real.exp_pos _).le
   have hZ x:0 ≤ Z x:=by unfold Z; split; exact ht' _; exact le_rfl
   change SumBudget Z _; refine ⟨hZ,Summable.of_finite,?_⟩
   rw [tsum_fintype,Fintype.sum_sum_type]; simp_rw [Fintype.sum_prod_type]; unfold loftCost; rw [add_zero]
   have hf x (h:waxV x=none): T x ≤ z*Real.exp π:=by rcases x with ⟨i,z⟩|⟨i,z⟩ <;> change z=none at h <;> subst z <;> (unfold T shells; simp only [waxV,Sum.elim_inl,Sum.elim_inr,if_true]; exact mul_le_mul_of_nonneg_left (one_more _ B he) hz) -- elaboration
   have hQ : (∑ x: Site f,∑ y:XMark f,Z (Sum.inl (x,y))) ≤ z*Real.exp π+F*AtomF.rays*2*(E*q):=by
    rw [sum_eq_single i]; rotate_left; · intro a _ ha; refine sum_eq_zero fun j _=> ?_; exact if_neg (by exact ha)
    · simp
    unfold Z; simp only [orbitM,Sum.elim_inl,if_true]; rw [Fintype.sum_option]; apply add_le_add (hf _ rfl)
    calc
     _ ≤ ∑ u:Support f,W (Sum.inl (i,some u))*Run.rent π b (punch i B (some u)) :=by
            refine sum_le_sum fun j _=>?_ ; have hg:= pax (B:=B) (F:=F) (i:=(0:Site c)) P he hb hv ht (Sum.inl (i,some j)); unfold T shells; rw [if_neg (by intro hx; change some j=none at hx; simp at hx)]; exact hg
     _ = F*AtomF.rays*2* ∑ u:Support f,crease i B P.coal i i (some u)*Run.rent π b (punch i B (some u)):=by rw [mul_sum]; apply sum_congr rfl; intro u _; exact mul_assoc _ _ _
     _ ≤ _:=mul_le_mul_of_nonneg_left ((cash_l P.att i i i B (Or.inl rfl) hp).trans (mul_le_mul_of_nonneg_left (even_wider P.att ..) (Real.exp_pos _).le)) (by have := ray_pos; positivity)
   have hx (x: Site c):(∑ j:XMark f,T (Sum.inr (x,j)))≤z*Real.exp π+t^2*fingers F^2*(2*(E*p)):=by
    rw [Fintype.sum_option]; apply add_le_add (hf (Sum.inr (x,none)) rfl)
    let y:= (S).embed x
    let C i j U:= crease y B P.knit i j (some U)*Run.rent π b (punch y B (some U))
    calc _ ≤ t^2*fingers F^2*(∑ U: Support f, ((∑ i,C x i U)+∑ i,C i x U)) :=by
            rw [mul_sum]; apply sum_le_sum; intro k _; unfold T shells; rw [if_neg (by intro hx; change some k=none at hx; simp at hx)]; apply le_trans (pax (i:=x) P he hb hv ht _); unfold level C; change t^2*fingers F^2*(_+_)*Run.rent _ _ (punch y B _) ≤_; simp_rw [mul_assoc (t^2*fingers F^2),add_mul,sum_mul]; exact le_rfl
         _ ≤ _:=by
            apply mul_le_mul_of_nonneg_left _ (by positivity); rw [sum_add_distrib,sum_comm (f:=fun U i=> C x i U), sum_comm (f:=fun U i=> C i x U),two_mul]; apply add_le_add
            · apply (sum_le_sum (fun i _=> cash_l P.arcP x i y B (Or.inl rfl) hp)).trans; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (P.arcP.spends x) (Real.exp_pos _).le
            apply (sum_le_sum (fun i _=> cash_l P.arcP i x y B (Or.inr rfl) hp)).trans; rw [← mul_sum]; exact mul_le_mul_of_nonneg_left (P.arcP.dues x) (Real.exp_pos _).le
   have hu : (∑ x: Site c,∑ j:XMark f, Z (Sum.inr (x,j)))≤z*Real.exp π+t^2*fingers F^2*(2*(E*p)):=by
    by_cases h:∃ x,(S).embed x=i
    · obtain ⟨x,hx'⟩:=h; rw [sum_eq_single x]; · apply le_trans (sum_le_sum fun j _=> ?_) (hx x); unfold Z; rw [if_pos]; exact hx'
      · intro j _ hj; exact sum_eq_zero fun u _=> if_neg (fun h=>hj ((S).embed_injective ((show (S).embed j=i from h).trans hx'.symm)))
      simp
    push Not at h; rw [show (∑ x: Site c,∑ j:XMark f,Z (Sum.inr (x,j)))=0 from sum_eq_zero (fun i _=>sum_eq_zero fun j _=> if_neg (h i))]; exact (sum_nonneg (s:= (univ:Finset (XMark f))) (fun j _=>ht' (Sum.inr (0,j)))).trans (hx 0)
   unfold E at *; linarith
end YM.QCD.Port
