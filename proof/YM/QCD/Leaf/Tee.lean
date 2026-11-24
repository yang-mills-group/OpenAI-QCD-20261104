import YM.QCD.Leaf.Emblem

/-! # fixed-basis actual now H̃. perturbation owns pole positive. small truncation powers. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Leaf.Tee
open Lat Kit Lattice Wilson Finset Function Filter Metric Tree RG Cost
open Orbit Birth Flume Sparks Leaf LeafM Quarry Stationary YM.Next.Free Pine Eyrie Revolve Rudder Garden Run Emblem
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {c f L n:Side}{D H: St f}{a b d h r η ξ δ ν A p C R V W E u q e m l G:ℝ}{j k B x:ℕ}
def blossomT (X:Offer 1 a A)(Y:Offer 2 d C) (ξ:ℝ): On:= wild (frosting X.W) ξ + wild (frosting Y.W) ξ

def roots (X:Offer 1 a A)(Y:Offer 2 d C): On:= X.lamp + Y.lamp
def trunkM (X:Offer 1 a A)(Y:Offer 2 d C) (ξ m:ℝ) (n:Side) : St n := blossomT X Y ξ n + (m:ℂ) • (1:St n)
lemma unity {J D H: Sheet n}(hp:Chiral J D)(h:Chiral J H): Chiral J (D+H):=by rw [Chiral,star_add,hp,h,mul_add,add_mul]
lemma tiedStar (X:Offer 1 a A)(Y:Offer 2 d C)(W:Grid n)(ha:0<a)(hd:0<d)(hp:0<ξ)(hx:ξ≤1): Chiral (chirality n) (trunkM X Y ξ m n W):=by
  have ht {k a C}(V: Offer k a C) (hv:0<a):Chiral (chirality n) (wild (frosting V.W) ξ n W):=(funds0 _).1 ((solidly _ V.price hp hx hv).lane _).symm
  apply unity (unity (ht X ha) (ht Y hd)); change star ((m:ℂ) • (1:Sheet n)) = _*((m:ℂ) • (1: Sheet n))*_; simp [chi_sq]
lemma kindsP (Q:Offer k a A)(ha:0 < a) (hp:0<ξ)(hx:ξ≤1): Tender (castF (wild (frosting Q.W) ξ n)) (castF (Q.lamp _)) (k+2) :=by
  have hs: 0<a/(1+k):=by positivity
  have hg:= buds (n:=n) _ hp hx (coined _ hs.le Q.price (by rw [div_mul_cancel₀ _ (by positivity)])) hs
  rw [presentation Q.W Q.bright Q.price] at hg; exact hg
lemma kinder (X:Offer 1 a A)(Y:Offer 2 d C)(ha:0<a)(hd:0<d)(hp:0<ξ)(hx:ξ≤1): Tender (castF (blossomT X Y ξ n)) (castF (roots X Y n)) 3:=by
  have ht:=kindsP (n:=n) Y hd hp hx; exact Transfer.accum _ _ _ (kindsP X ha hp hx) _ ⟨fun i hi=> ht.1 i (by omega),ht.2⟩
lemma vaultP (ha:0<a)(hd:0<d)(hb:0≤b)(C A:ℝ):∃ δ T:ℝ,∃ n:ℕ,0<δ∧0<T∧∀ X : Offer 1 a A,∀ Y:Offer 2 d C, ∀ q:Side,∀ B:ℕ,n≤B→∀ ξ m:ℝ,0<ξ→ξ≤1→Own q (δ*ξ^2) b B (trunkM X Y ξ m q) (T*(ξ+|m|)):=by
  obtain ⟨e,Q,N,hq,hP,H⟩:=richP 1 ha hb
  obtain ⟨x,L,M,hx,hL,I⟩:=richP 2 hd hb
  let T:=1+Q*|A|+L*|C|+Real.exp b; have hh:0<T:=by unfold T; positivity
  refine ⟨min e x,T,max N M, lt_min hq hx,hh,fun X Y f B hp ξ m hz hr=>?_⟩
  have he : 0≤ A:=(tsum_nonneg (fun i=> (X.W i).price_nn.trans ((X.W i).paidUp ha.le))).trans X.price.bill; have hd : 0 ≤ C:=(tsum_nonneg (fun i=> (Y.W i).price_nn.trans ((Y.W i).paidUp hd.le))).trans Y.price.bill
  apply (((H _ _ _ X.price ξ hz hr f B ((le_max_left ..).trans hp)).clip (mul_le_mul_of_nonneg_right (min_le_left ..) (by positivity))).plus ((I _ _ _ Y.price ξ hz hr f B ((le_max_right ..).trans hp)).clip (mul_le_mul_of_nonneg_right (min_le_right ..) (by positivity)))|>.plus ((Heritage.heritage_one _ hb).scalar (m:ℂ))).mono
  rw [pow_one,Complex.norm_real,Real.norm_eq_abs]; unfold T; rw [abs_of_nonneg he,abs_of_nonneg hd]; have hJ : L*C*ξ^2≤ L*C*ξ:= mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hz.le hr (by omega : 1 ≤ 2) |>.trans_eq (pow_one _)) (by positivity); nlinarith [Real.exp_pos b,mul_nonneg (show 0≤1+Q*A+L*C by positivity) (abs_nonneg m)]

variable {E₀: Flight j k}{P:Plan j}{hE:f.val=c.val*E₀.L.val}
local notation "S"=> St f
abbrev zoom (w:ℝ) (H:St f):St f:=fun x=>notch w (H x)
def pesto (P:Plan j)(F: Flight j k)(h:f.val=c.val*F.L.val)(X: St f): St f:=vaultF P F h 0+ X
structure Chest (L:Side) (n:ℕ)(b w q g G Y e:ℝ)(a:ℝ)(P:Plan j)(k:ℕ) : Prop where
 grades : 0<w ∧ 0 ≤ q ∧ q <1 ∧ 0 < g ∧ g<1 ∧ 0<G ∧0<Y ∧ 0<e ∧0<a
 buy (F: Flight j k)(hr:F.L=L) (s f:Side)(h:f.val=s.val*F.L.val)(B:ℕ)(he:n≤B)(X: St f)(δ:ℝ):0<δ→δ ≤ e→Own f δ b B X a → let D:= zoom w (pesto P F h X)
      Wing (sliceL F h) (tied F h 0) δ b B Y ∧ (∀ U,‖D U‖ ≤ q) ∧ (∀ i:ℕ, Own f δ b B (D^i) (G*g^i))

lemma premiere (P:Plan j) (L:Side) (k:ℕ)(b:ℝ)(hb:0≤b): ∃ w q g G Y e a n,Chest L n b w q g G Y e a P k:=by
  obtain ⟨w,q,g,G,e,Y,n,R⟩:= groves P L k hb; have he:= R.pos; have hh:= R.ceil; have hl:= R.safe; have hg:= R.pays; have ht:=R.grade; have hG:=R.solid
  let r:=min ((1-q)/2/w) ((1-g)/2/G/w); have hr : 0 < r:=lt_min (by exact div_pos (by linarith) he) (div_pos (div_pos (by linarith) hG) he)
  have hR:= sub_pos.mpr R.ceil; have hh': w*r ≤ (1-q)/2:=by rw [mul_comm]; exact (le_div_iff₀ he).1 (min_le_left ..)
  have hM: G*(w*r)≤ (1-g)/2:=by rw [mul_comm w,mul_comm]; exact (le_div_iff₀ hG).1 ((le_div_iff₀ he).1 (min_le_right ..))
  refine ⟨w,q+(1-q)/2,g+(1-g)/2,G,Y,e,r,n, ⟨⟨he,by linarith,by linarith,by linarith,by linarith,hG,R.soaring,R.tube,hr⟩,fun F hZ s f h B H₀ X δ ht' hy hu=>?_⟩⟩
  obtain ⟨hp,hv,hm⟩:= R.uses F hZ s f h B H₀ 0
  have heq: zoom w (pesto P F h X)=zoom w (vaultF P F h 0)+(- (w:ℂ)) • X:=by ext1 U; simp only [zoom, notch,pesto,Pi.add_apply,Pi.smul_apply]; simp [smul_add,sub_eq_add_neg, add_assoc]; abel
  have hf : Own f δ b B ((- (w:ℂ)) • X) (w*r):=by simpa only [norm_neg,Complex.norm_real,Real.norm_of_nonneg he.le] using hu.scalar (- (w:ℂ))
  dsimp only; rw [heq]; refine ⟨⟨hp.1.clip hy,hp.2.clip hy⟩,?_,?_⟩
  · intro U; have h: ‖zoom w (vaultF P F h 0) U‖≤q:=hv U; rw [Pi.add_apply]; apply (norm_add_le ..).trans; exact (add_le_add h (hf.value ht' hb (by positivity) U)).trans (add_le_add_right hh' _)
  intro i; exact Emblem.adds (D:=zoom w (vaultF P F h 0)) (fun i=>(hm i).clip hy) hf ht' hb hg.le (by linarith) (mul_pos he hr) hG (by linarith) i
end YM.QCD.Leaf.Tee
