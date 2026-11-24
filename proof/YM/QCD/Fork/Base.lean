import YM.QCD.Fork.Truffle
/-! # full row ledgers at GOOD and away
Claims purchase real sup per slot, not costs at one field. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Fork
open Lat Kit Lattice Wilson RG Run Leaf Tee Function Finset Metric Filter
open Orbit Flume Sparks Quarry Pine QCD.Cost Eyrie Revolve Rudder Garden
open YM.Next.Free Laurent LeafM
open scoped Topology BigOperators Matrix Matrix.Norms.L2Operator ContDiff Classical
variable {L f c:Side}{t p η ξ w r q R u v C D G m A μ κ d:ℝ}{B b j k l:ℕ}{F:Flight j k}{P:Plan j}{e:f.val=c.val*F.L.val} {X: Offer 1 u C}{a₂:ℝ}{Qb:Offer 2 v a₂}{a:ℝ}
local notation "S"=> sliceL F e
local notation "T"=> pesto P F e (trunkM X Qb ξ m f)
-- capacities
variable {z: Land f (Site f) (Site c)}{y:Pays f (Site f) (Site c)}{z': Land f (Site c) (Site f)}{y':Pays f (Site c) (Site f)}
-- orientation free via arguments. phase law in Pack.Crop when transpose not required. H'}
structure West (M: Ratio c f)(o:Site f)(P:Site c→ Pulse f→Bundle)(s:ℕ) (K t:ℝ)(g d:ℝ)(m:ℕ):Prop where
 leases : ∃ W: Site c→ℝ, 0 ≤ W∧ (∑ j,meets M o m j*W j) ≤ K∧∀ (U:Grid f),nearby U o (s+1) t→∀ j,‖P j (settled U)‖ ≤ W j
 position (i : Site c) : M.embed i ∉ trunkFt o s →∀ U, P i (settled U) = 0
 stocks : ∃ Q:Site c→ℝ, 0≤ Q∧∑ j,Q j ≤ g ∧∀ Y∈Kingdom f d,∀ j,‖P j Y‖ ≤ Q j

-- R b angular g large always even fine derivative factors inherited to be recovered in parks
lemma later (x:Site f)(F:Ratio c f)(P':Site c→Pulse f→Bundle)(l:ℕ) (H χ : Site c→ℝ) (hP:‖H‖≥0) (ht : 0≤ H)(hQ:0 ≤ χ) (hg:∑ i,H i≤ p)(hh:∑ i,meets F x l i*χ i≤ D)
    (hy:0 ≤ ξ)(hv:0<κ)(hw:0≤w)(he:0≤η)
    (h : ∀ Z∈ Kingdom f κ,∀ i, ‖P' i Z‖ ≤ H i) (hx : ∀ i,F.embed i ∉ trunkFt x b→∀ U : Grid f, P' i (settled U)=0)
    (hl : ∀ (U:Grid f), nearby U x (b+1) ξ→∀ i, ‖P' i (settled U)‖ ≤ χ i+w + η * H i):
    West F x P' b (D+(1+(b+1:ℝ))^l*(2*(b:ℝ)+1)^4*w+(1+(b+1:ℝ))^l*η*p) ξ p κ l:=by
  let G i:=if i ∈ spanM F x b then χ i+w+η*H i else 0
  refine ⟨⟨G,fun i=>by unfold G; split; exact add_nonneg (add_nonneg (hQ i) hw) (mul_nonneg he (ht i)) -- switched
                                                ; exact le_rfl, ?_,fun U p i=>?_⟩,hx,⟨H,ht,hg,h⟩⟩
  · let L i:=G i • (1:Bundle); have heG i:0 ≤ G i:= by unfold G; split; exact add_nonneg (add_nonneg (hQ i) hw) (mul_nonneg he (ht i)); exact le_rfl
    have heq i : ‖L i‖=G i:=by simp only [L,norm_smul,oneNorm,mul_one,Real.norm_of_nonneg (heG _)]
    let Z (i):Bundle:=χ i • (1:Bundle); have hZ i : ‖Z i‖=χ i:=by simp only [Z,norm_smul,oneNorm,mul_one,Real.norm_of_nonneg (show 0≤χ i from hQ _)]
    simp_rw [←heq]; exact forward (t:=η) x F b l L Z 0 H _ _ _ _ (by simp_rw [hZ]; exact hh) le_rfl hg ht (by exact le_trans (sum_nonneg (fun i _=>ht i)) hg) hw he (fun i hi=> by rw [hZ, heq, show G i=_ from if_pos hi]) (fun i hi=>by unfold L; rw [show G i=0 from if_neg hi]; exact zero_smul ..)
  unfold G; split
  next hi=> exact hl U p i
  next hi=> rw [hx i (fun hk=> hi (mem_filter.mpr ⟨mem_univ _,hk⟩)),norm_zero]

abbrev Sea (F:Flight j k)(h:f.val=c.val*F.L.val)(s: ℕ)(r:ℝ) (K D t:ℝ)(z: Land f (Site f) (Site c))(z': Land f (Site c) (Site f))(m:ℕ):Prop :=∀ x, West (sliceL F h) x (fun i=>spoon z x s x i) s K t D r m∧ West (sliceL F h) x (fun i=>spoon z' x s i x) s K t D r m

def tabP (P:Plan j)(L: Side)(D R A a r p m t δ:ℝ)(l b B:ℕ):ℝ:=D*slope L/(L.val:ℝ)+(1+(b+1:ℝ))^l*(2*(b:ℝ)+1)^4*(stamp P L*m*a⁻¹*massL L)+(1+(b+1:ℝ))^l*(Real.exp (-r*fossil b B)+ (δ/2)⁻¹*A*(b+1:ℝ)^5*t)*R
lemma horns (b l B:ℕ)(hp:r>0) (ht:0≤ t) (he:0<η) (hs:Species F e p R η r a B T)
   (hP:Pack id (S).embed η r B (rightL F e T) R z y)(hQ:Pack (S).embed id η r B (leftL F e T) R z' y')
   (Xh:∀ x:Site f,(∑ i:Site c,meets S x l i * ‖cell (proton F e) x i‖)≤D * slope F.L/(F.L.val:ℝ)∧∑ i:Site c,meets S x l i * ‖cell (barP F e) i x‖≤D*slope F.L/(F.L.val:ℝ))
   (hA: 0<A)(hD: A*(b+1:ℝ)^5*t <η/2)(hv : ∀(U: Grid f) (o:Site f),nearby U o (b+1) t →∃ W: Frame f, ‖settled (rider (gauge W U) b o)-settled 1‖ ≤ A*(b+1:ℝ)^5*t): Sea F e b η (tabP P F.L D R A a r p |m| t η l b B) R t z z' l:=by
  intro o
  let M:=stamp P F.L*|m| *a⁻¹*massL F.L; let Q:=A*(b+1:ℝ)^5*t; have hm:0≤M:=by unfold M; have := healthy P F.L; have hx:=hs.calf; have he:=mass_pos F.L; positivity
  have hq:0 ≤ Q:=by unfold Q; positivity
  have hx(g:ℝ)(Xg:Support f) (Y:Pulse f→Bundle)(U) (s u:Site f)(w:ℝ)(hp:Crop s u η Xg Y g)(h:s∉Xg∨u∉Xg): Y (settled U)=0:=by
    by_contra! hv; have ht := (norm_pos_iff.mpr hv).trans_le (hp.2.2.2.1 (settled U) (citizenship f he U)); have hm:=(hp.2.1 ht.ne'); tauto
  let Y := Real.exp (-r*fossil b B)+(η/2)⁻¹*A*(b+1:ℝ)^5*t -- const simplify
  have hY : 0 ≤ Y :=by unfold Y; positivity
  constructor
  · let J (i:Site c):=duel y o i r B
    let E i:= ‖cell (proton F e) o i‖
    refine later o (S) _ l J E (norm_nonneg _) ?_ (fun i=>norm_nonneg (cell (proton F e) o i)) (hP.spends o) (Xh o).1 ht he hm hY ?_ ?_ ?_
    · intro i; exact (le_trans (trimming hP o b o i).1 (coins hP o b o i hp.le))
    · intro Z h i; exact ((trimming hP o b o i).2.2.2.1 Z h).trans (coins hP o b o i hp.le)
    · intro i h U; exact hx _ _ _ U _ _ 0 (trimming hP o b o i) (Or.inr h)
    intro U H i; obtain ⟨zV,hz⟩:=hv U o H
    have hh:=payProbe (trimming hP o b o i) hz hD he
    have hx : ‖spoon z o b o i (settled 1)‖ - ‖cell (rightL F e T 1) o i‖ ≤ _:= (norm_sub_norm_le ..).trans (mismatch hP o i b o (Or.inl rfl) hp.le he _)
    have hf : ‖cell (rightL F e T 1) o i‖-E i≤ M:= (norm_sub_norm_le ..).trans ((fees hs).1 o i)
    change _ ≤ E i + M + Y*J i; have hr : charge y o b o i / (η/2)*Q ≤ (J i)/(η/2)*Q :=mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (coins hP o b o i hp.le) (half_pos he).le) hq
    dsimp only [Q, J, Y, E] at *; simp only [div_eq_mul_inv] at *; linarith only [hh,hx,hf,hr]
  · let J (i:Site c):=duel y' i o r B
    let E i:= ‖cell (barP F e) i o‖
    refine later o (S) _ l J E (norm_nonneg _) ?_ (fun i=>norm_nonneg (cell (barP F e) i o)) (hQ.dues o) (Xh o).2 ht he hm hY ?_ ?_ ?_
    · intro i; exact (le_trans (trimming hQ o b i o).1 (coins hQ o b i o hp.le))
    · intro Z h i; exact ((trimming hQ o b i o).2.2.2.1 Z h).trans (coins hQ o b i o hp.le)
    · intro i h U; exact hx _ _ _ U _ _ 0 (trimming hQ o b i o) (Or.inl h)
    intro U H i; obtain ⟨zV,hz⟩:=hv U o H
    have hh:=payProbe (trimming hQ o b i o) hz hD he
    have hx : ‖spoon z' o b i o (settled 1)‖ - ‖cell (leftL F e T 1) i o‖ ≤ _:= (norm_sub_norm_le ..).trans (mismatch hQ i o b o (Or.inr rfl) hp.le he _)
    have hf : ‖cell (leftL F e T 1) i o‖-E i≤ M:= (norm_sub_norm_le ..).trans ((fees hs).2 i o)
    change _ ≤ E i + M + Y*J i; have hr : charge y' o b i o / (η/2)*Q ≤ (J i)/(η/2)*Q :=mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (coins hQ o b i o hp.le) (half_pos he).le) hq
    dsimp only [Q, J, Y, E] at *; simp only [div_eq_mul_inv] at *; linarith only [hh,hx,hf,hr]
end YM.QCD.Fork
