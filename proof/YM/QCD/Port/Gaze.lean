import YM.QCD.Port.Beacon
/-! # estimates for pieces. Δ at stationary flat kernels subtracted. Cost between tiny and expensive. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Port
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run Tree
open Leaf Tee Flume Orbit Quarry Stationary Fork Pine YM.Next.Free Push.Local
open Jets Sun Revolve Garden Bay Strut LeafM Paths Metric Extra AtomF
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {f c:Side}{F:ℕ}{u v η ξ t p C D A R z q w Ω:ℝ}{b B:ℕ}{j k:ℕ}{L:Flight j k}{J:Plan k}{H:f.val=c.val*L.L.val}{X:St f}{W:ℕ→Atom su 2}
local notation "Mx"=> Modes c F
local notation "S"=> sliceL L H
variable (P : Swathe L H X W J u v η p q b)
-- full post bounds with infrastructure. `m` large. form negative.
def level (F B:ℕ)(y:ℝ) : Varn f c →ℝ:= Sum.elim (fun i=> F*AtomF.rays*2*crease i.1 B P.coal i.1 i.1 i.2) fun i=> y^2*fingers F^2*((∑ j,crease ((S).embed i.1) B P.knit i.1 j i.2)+∑ j,crease ((S).embed i.1) B P.knit j i.1 i.2)
lemma lux (F B:ℕ)(U:Grid f)(ht:0<v)(hy:0<t) (x:Varn f c):load (fun _=>t) (light _ (sliceF P F B x U)) ≤ level P F B t x:=by
   rcases x with ⟨i,z⟩|⟨i,z⟩
   · refine (readout ..).trans ?_; unfold level; dsimp only [Sum.elim]; unfold chalkF; rw [mul_assoc (F:ℝ),mul_assoc (F:ℝ)]; apply mul_le_mul_of_nonneg_left _ (by positivity); rw [← Matrix.trace_sub]; apply (chalkSize _).trans; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ ray_pos.le; have he:= (cups P.att i i i B z).2.2.2.1; rw [two_mul]; exact (norm_sub_le ..).trans (add_le_add (he _ (citizenship f ht U)) (he _ (citizenship f ht 1)))
   exact farm_price P F B i U z ht hy _ _ (fun i'=> (cups P.arcP _ _ _ B z).2.2.2.1 _ (citizenship f ht U)) (fun i'=> (cups P.arcP _ _ _ B z).2.2.2.1 _ (citizenship f ht U))
lemma grew (x:Varn f c)(hv:0<v)(ht:0<t):0 ≤level P F B t x:=(load_nn ..).trans (lux P F B 1 hv ht x)
lemma even_wider {P Q:Type*} [Fintype P][Fintype Q]{M:Grid f→ArrayL P Q} {G: Land f P Q}{C:Pays f P Q}{w:P→Site f}{b':Q→Site f}(h:Pack w b' v η b M q G C)(i j): duel C i j η b ≤q:=
  (single_le_sum (s:=univ) (f:=fun j=>duel C i j η b) (fun j _=>sum_nonneg (fun u _=> mul_nonneg (Real.exp_pos _).le (h.crop i j u).1)) (mem_univ _)).trans (h.spends i)
lemma root_all (x:Varn f c)(hp:waxV x=none) (hv:0≤η): level P F B t x ≤ max (F*AtomF.rays*2*q) (t^2*fingers F^2*(2*p)) := by
   rcases x with ⟨i,z⟩|⟨i,z⟩ <;> change z=none at hp <;> subst z
   · apply le_trans _ (le_max_left ..); apply mul_le_mul_of_nonneg_left ((coins P.att i B i i hv).trans (even_wider P.att i i)); have ht:=ray_pos; positivity
   apply le_trans _ (le_max_right ..); apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _)); rw [two_mul]; exact add_le_add ((sum_le_sum (fun a _=> coins P.arcP _ B i a hv)).trans (P.arcP.spends i)) ((sum_le_sum (fun a _=>coins P.arcP _ B a i hv)).trans (P.arcP.dues i))

lemma scalar_trim (F B:ℕ)(U:Grid f) (x:Site f)(e:Frame f)(hv:0<v)(he:‖settled (rider (gauge e U) B x)-settled 1‖ ≤Ω)(hz:Ω<v/2)(hp:0≤η):
 load (fun _=>t) (light _ (sliceF P F B (.inl (x,none)) U)) ≤ F*(AtomF.rays*(q/(v/2)*Ω)):=by
  apply (readout ..).trans; apply mul_le_mul_of_nonneg_left _ (by positivity)
  let V := rider (gauge e U) B x
  let c:= Fork.charge P.coal x B x x; let M:=chipK x B P.walk x x none
  have ha:=trimming P.att x B x x
  let A := touch (colour (e x)); have hA : A∈unitary _:=touch_u (x:=colour (e x)) ⟨su.mat_star_mul _,su.mat_mul_star _⟩
  have hh:M (settled V)=A*M (settled U)*star A:=(ha.2.2.2.2.1 (gauge e U) V (fit x B)).symm.trans (ha.2.2.2.2.2 U e)
  have ht:(M (settled U)).trace=(M (settled V)).trace := by rw [hh,Matrix.trace_mul_comm,← mul_assoc,hA.1,one_mul]
  change ‖(M (settled U)).trace-_‖ ≤_; rw [ht,← Matrix.trace_sub]; apply (chalkSize ..).trans; apply mul_le_mul_of_nonneg_left _ ray_pos.le
  have hf (i) (h : i∈ ball (settled (1:Grid f)) v): i∈ Kingdom f v := Set.mem_iUnion.mpr ⟨1,h⟩
  have hP : settled V∈ball (settled (1:Grid f)) (v/2):=by rw [Metric.mem_ball,dist_eq_norm]; exact he.trans_lt hz
  have hX:0≤c:=ha.1
  have hG:= (coins P.att x B x x hp).trans (even_wider P.att x x)
  apply (lastwig M hv (fun i h'=> ha.2.2.1 _ (hf i h')) (R:=c) (fun i h'=> ha.2.2.2.1 _ (hf i h')) hP).trans; apply mul_le_mul _ he (norm_nonneg _) ((show 0 ≤ c/(v/2) by positivity).trans ?_); all_goals exact div_le_div_of_nonneg_right hG (half_pos hv).le

lemma crop_p (F B:ℕ)(U:Grid f)(x:Site c)(e:Frame f)(hy:0<v)(he:‖settled (rider (gauge e U) B ((S).embed x))-settled 1‖ ≤Ω)(hz:Ω<v/2)(hp:0≤η)(hx:‖dusk L H J X 1‖ ≤ C):
  let a (i j:Site c):= ‖chipK ((S).embed x) B P.bath i j none (settled U)‖
  let R:= (2*(B:ℝ)+1)^4*C+(Real.exp (-η*fossil B b)+(v/2)⁻¹*Ω)*p
  (∑ j,a x j)≤R ∧ (∑ i,a i x) ≤ R:=by
  intro a R; let y:= (S).embed x; let o:=spanM S y B
  let η':=Real.exp (-η*fossil B b); have hη:0<η':= Real.exp_pos _; have hΩ: 0 ≤ Ω:=(norm_nonneg _).trans he; let φ:= η' + (v/2)⁻¹*Ω; have hv:0≤φ:= by unfold φ; positivity
  have hC:0≤C:=(norm_nonneg _).trans hx
  let D (i j:Site c):= duel P.knit i j η b
  have hd i j:0≤ D i j:=(trimming P.arcP y B i j).1.trans (coins P.arcP y B i j hp)
  have hf i j: (i=x∨ j=x) → a i j≤ C+φ*D i j:=by
    intro t; let Z:=spoon P.bath y B i j
    have hm:= trimming P.arcP y B i j
    have hP:=payProbe hm he hz hy; let Y:= cell (dusk L H J X 1) i j
    have hs : ‖Z (settled 1)‖-‖Y‖ ≤η'*D i j:=(norm_sub_norm_le ..).trans (mismatch P.arcP i j B y (by rcases t with rfl|rfl <;> simp [y]) hp hy _)
    have hX : ‖Y‖≤C:=(cell_pay ..).trans hx; have hi:= coins P.arcP y B i j hp
    change ‖spoon P.bath y B i j (settled U)‖ ≤_; have hh:= mul_le_mul_of_nonneg_right hi (show 0 ≤ (v/2)⁻¹*Ω by positivity); unfold φ D; simp only [Z,Y,D, div_eq_mul_inv] at hP hs hX hh ⊢; linarith only [hP,hs,hX,hh]
  have hzero i j (h:i∉o ∨ j∉o):a i j=0:=by
    by_contra! H; have hx :0<a i j:=lt_of_le_of_ne (norm_nonneg _) (Ne.symm H)
    have hh:=trimming P.arcP y B i j; have ht:=hh.2.1 ((hx.trans_le (hh.2.2.2.1 _ (citizenship f hy U))).ne'); exact h.elim (fun h=>h (mem_filter.mpr ⟨mem_univ _,ht.1⟩)) fun h=>h (mem_filter.mpr ⟨mem_univ _,ht.2⟩)
  have h (X Y : Site c→ℝ)(hh:∀ i,i∉o→ X i=0)(he:∀ i,X i≤ C+φ*Y i)(hy:0 ≤ Y) (hp:∑ i,Y i≤p): ∑ i,X i ≤R:=by
    rw [← sum_subset (subset_univ o) (fun i _=> hh i)]; apply (sum_le_sum (fun i _=> he i)).trans; rw [sum_add_distrib,sum_const,nsmul_eq_mul,← mul_sum]; apply add_le_add (mul_le_mul_of_nonneg_right (Fork.olives S y) hC); exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg (subset_univ o) (fun i _ _=>hy i)).trans hp) hv
  exact ⟨h _ (D x) (fun i ht=>hzero x i (Or.inr ht)) (fun i=> hf x i (Or.inl rfl)) (hd x) (P.arcP.spends x),h _ (fun i=>D i x) (fun i ht=>hzero i x (Or.inl ht)) (fun i=>hf i x (Or.inr rfl)) (fun i=> hd i x) (P.arcP.dues x)⟩
end YM.QCD.Port
