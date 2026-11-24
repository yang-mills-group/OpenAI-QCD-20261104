import YM.Oriole.Lodge
import YM.Oriole.Rhea
/-! dual reads hue averaging, with all weights explicit. 
 `spread uncoat = -horn` per fiber.M. -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Oriole
open QCD QCD.Lat QCD.Grass Lattice TensorProduct Function UV PCAC Filter MeasureTheory RG
open scoped BigOperators Topology Matrix Matrix.Norms.L2Operator ContDiff Classical TensorProduct
variable {d n:ℕ}(a b:Flavor 6)(g:Bool){c:Side}
open Poised.Display Poised.Stative Module Finset Revolve SourceRead Patria TorusPCAC.Geometry Cylinder
local notation "Q"=> Massive.Run.plane
local notation "T"=> Lat.Fiber
variable (x:Lat.Fields c 6)(F:Taper)(M:Spike)(h:ℝ)
local notation "D"=> piece a b (uncoat x)
local notation "V"=> wave M
noncomputable def massM(M:Spike):ℝ:=∑ i:T,∑ j:T,‖wave M i j‖
lemma e_bud : 0≤ massM M := sum_nonneg fun _ _=> sum_nonneg fun _ _=> norm_nonneg _
noncomputable abbrev PP (x y:Site c):=star (Massive.Run.plane x)*Massive.Run.plane y
noncomputable abbrev TP (T₀:Taper)(x y:Site c) := Np T₀ x*Np T₀ y
noncomputable def diffS (a b:Flavor 6)(M:Spike)(T₀:Taper): Lat.Fields c 6→ₗ[ℂ]ℂ:= spread a b PP M-spread a b (TP T₀) M
local notation "Γ"=> normCost/(c.val:ℝ)
noncomputable abbrev yieldS(M:Spike)(c:Side) :=massM M*(normCost/(c.val:ℝ))*2
lemma screen (hr:1 ≤ h)(hn:1≤ n) : ‖diffS a b M F x‖ ≤ yieldS M c * MassiveQCD.Plate.view 0 n x h:=by
    rw[diffS,LinearMap.sub_apply]; change ‖(∑ i: Site c,∑ j:Site c,_)-(∑ i:Site c,∑ j:Site c,_)‖ ≤ _; rw [←sum_sub_distrib]; simp_rw [←sum_sub_distrib,←sub_mul,Matrix.trace,Matrix.diag_apply,Matrix.mul_apply, Finset.mul_sum]
    let f(p q: Site c)(i j:T):= (PP p q-TP F p q)*(QCD.Run.cell D p q i j* V j i)
    have he : (∑ p:Site c,∑ q:Site c, ∑ i:T,∑ j:T,f p q i j)=∑ i:T,∑ j:T,∑ p:Site c,∑ q:Site c, f p q i j:=by
          let hp := sum_comm (s:= (univ:Finset (Site c × Site c))) (t:=(univ:Finset (T × T))) (f:=fun p i=> f p.1 p.2 i.1 i.2); simpa only [Fintype.sum_prod_type] using hp
    rw [he]; let u(i j:T):=‖V j i‖; let s:=MassiveQCD.Plate.view 0 n x h
    have hp(i j:T): ‖∑ p:Site c,∑ q: Site c,f p q i j‖ ≤ u i j*Γ*2*s:=by
          apply (norm_sum_le ..).trans; apply (sum_le_sum (fun p _=> norm_sum_le (s:=(univ:Finset (Site c))) (fun q=>f p q i j))).trans
          rw [mul_assoc (u i j*Γ) 2 s]; apply (le_trans (b:= u i j*Γ*(∑ p:Site c,∑ q:Site c,(pdist p+pdist q:ℝ)*‖QCD.Run.cell D p q i j‖)) _ (mul_le_mul_of_nonneg_left (le_budget a b x h i j hr hn) (by unfold u; have hc:=cost_pos; positivity))); simp_rw [Finset.mul_sum]; refine sum_le_sum fun p _=> sum_le_sum fun q _=>?_ ; unfold f; simp_rw [norm_mul]; exact (mul_le_mul_of_nonneg_right (variety p q F) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).trans_eq (by unfold u; ring)
    refine (norm_sum_le ..).trans (le_trans (b:=∑ i:T,∑ j:T,u i j*Γ*2*s) (sum_le_sum fun i _=> (norm_sum_le ..).trans (sum_le_sum fun j _=> hp ..)) ?_); unfold yieldS massM; simp_rw [Finset.sum_mul]; rw [sum_comm]
-- extraction orientation.Translates weighted. identity origin H.S.
variable (P Y: Density c 6)(X:Label 8)(H:TaperHol)
local notation "Φ"=> (Canvas.foil P Y) 1
local notation "V₀"=> juncoat X.val
local notation "ν"=>Fintype.card Lat.Fiber
local notation "I"=> (0:Multi 8)
local notation "N₀"=>T -- Fiber
lemma zeroN (s:Site c): Nw F I s=Np F s:=by unfold Nw; rw [show SourceRead.profile I (Lattice.lift s) 1=1 from by have he(i:Axis):power I i=0:=rfl; simp [SourceRead.profile,he],mul_one]
lemma y_K(X:CensusA 8)(i j: Multi 8)(H':i≠I∨j≠I)(B:Bundle): Oriole.prism a b I I (fieldB a b i j B)=0:=by ext u v; unfold Oriole.prism; rw[Matrix.of_apply,fieldK]; rcases H' with h|h <;> simp [h,h.symm]
local notation "Jx" x:arg=> juncoat x
local notation "Gc"=> pulp g
local notation "F₀"=> flame a b g 8 (by norm_num)
local notation "L"=> arbor a b g
lemma z_stroke(t:Bool) : Oriole.prism a b I I (juncoat (L t).val) = 0:=by
     rw [arbola a b g t]; simp_rw [← j_stard, map_sum, j_coat]
     ext i j; unfold Oriole.prism; rw [Matrix.of_apply, Matrix.sum_apply]; change (∑ x:Axis,_)=0; refine sum_eq_zero fun q _=>?_ ; rw [fieldK]; cases t <;> simp [one_jet,highV q,(highV q).symm]
lemma z_io(r p q:ℂ) : Oriole.prism a b I I (juncoat (r • (F₀).val+p • (L true).val+q • (L false).val))=r • wave Gc:=by
     let f: CensusA 8→ₗ[ℂ]Bundle:= {toFun:=Oriole.prism a b I I,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}; change f (juncoat (r • bilinear _ _ Gc _ _+ _+ _))= _; simp_rw [map_add,map_smul]; rw [show f (juncoat _)= 0 from z_stroke a b g true, show f (juncoat _)= 0 from z_stroke a b g false,smul_zero,smul_zero,add_zero,add_zero,← j_stard,j_coat,show f _=_ from coreB a b I I (wave Gc)]
lemma orbitZ (r p q:ℂ)(hz:X=r • F₀+p • L true+q • L false)(hX:Tally H 0 X P Y): spread a b (TP H.T) Gc Φ= ν * r :=by
     let T':= Oriole.prism a b I I V₀; have hG:T'=r • wave Gc:=by unfold T'; rw [hz]; exact z_io ..
     let S:=wave Gc; have hg:T'*S=r • (1:Bundle):= by rw[hG,Matrix.smul_mul,wave_mul,P_sq,wave_one]
     let u:= uncoat Φ; let K':=H.T
     have hB(i j: Lat.Fiber) : T' i j=∑ p:Site c,∑ q:Site c, TP H.T p q* QCD.Run.cell (piece a b u) p q i j:=by
          have ht:= script _ P Y X hX ((I,i),a) ((I,j),b) (by change spinWeight I+spinWeight I≤_; rw [cost_root]; norm_num); simp_rw [zeroN] at ht; exact ht
     have hu : T'= ∑ p:Site c,∑ q:Site c, TP H.T p q • QCD.Run.cell (piece a b u) p q:=by ext i j; simp_rw [Matrix.sum_apply,Matrix.smul_apply]; exact hB i j
     have hz : (T'*S).trace=r*ν:=by rw[hg,Matrix.trace_smul,Matrix.trace_one]; rfl -- trace_one
     rw [hu,Matrix.sum_mul, Matrix.trace_sum] at hz; simp_rw [Matrix.sum_mul, Matrix.trace_sum, Matrix.smul_mul,Matrix.trace_smul] at hz; exact hz.trans (mul_comm ..)
open TorusPCAC.Ward QCD.Grass.Ward
lemma primal (Y: Density c 6) (hp:Plus (P 1))(hz:IsUnit (P 1))(hy:coef ∅ (Y 1)=0)(M:Spike) : Fintype.card (Site c)* ν * horn M a b (Stiffness.body P 1) (Y 1) = - (spread a b PP M (Canvas.foil P Y 1)) :=by
      have he:Y 1=P 1*Canvas.foil P Y 1:= (Ring.mul_inverse_cancel_left _ _ hz).symm -- missing hz
      let Yt:=Canvas.foil P Y 1; let v:=Stiffness.body P 1; have hQ:v≠0:=zeroR_unit (P 1) hz
      have ht : zeroR Yt=0:=by apply (mul_eq_zero.mp (?_ : v*zeroR Yt=0)).resolve_left hQ; rw [show v*zeroR Yt= _ from (zeroR_mul ..).symm,← he]; exact hy
      have hh: traceP (Y 1)= - v • uncoat Yt:=by
           nth_rw 1[he]; ext i j; have hv: two (P 1 * Yt) (Sum.inl j) (Sum.inr i)= v*two Yt (Sum.inl j) (Sum.inr i):=by rw [two_mul_form _ _ Yt hp,ht,mul_zero,zero_add]; rfl
           change - (two (_*Yt) _ _)=(-v)*(- - two _ _ _); rw[hv]; ring
      rw [horn,hh]; unfold spinTest; have hu : piece a b (- v • uncoat Yt)=- v • piece a b (uncoat Yt):=rfl; rw [hu]; simp_rw [show ∀ i j:Site c,QCD.Run.cell (-v • piece a b (uncoat Yt)) i j=- v • QCD.Run.cell (piece a b (uncoat Yt)) i j from fun i j=>rfl,Matrix.smul_mul,Matrix.trace_smul]
      let Wt:=spread a b PP M Yt; let C:ℂ:=Fintype.card (Site c); let q:ℂ:=ν; let f:=fun i j:Site c=> spinTest M i j (piece a b (uncoat Yt)); have hw:-v*Wt=∑ i:Site c,∑ j: Site c, star (Q i) * (-v • f i j) * Q j:=by
           unfold Wt; change -v* ∑ i:Site c,∑ j: Site c,PP i j*f i j= _; simp_rw [mul_sum]; refine sum_congr rfl fun i _=>sum_congr rfl fun j _=>?_ ; unfold PP; simp only [smul_eq_mul]; ring
      rw[← hw]; change C*q* (-v*Wt/v/(C*q))=-Wt; have hC:C≠0:=Nat.cast_ne_zero.mpr Fintype.card_pos.ne'; have hν:q≠0:=Nat.cast_ne_zero.mpr Fintype.card_pos.ne'; field_simp
end YM.Massive.Oriole
#print axioms YM.Massive.Oriole.primal
#print axioms YM.Massive.Oriole.orbitZ
#print axioms YM.Massive.Oriole.screen
