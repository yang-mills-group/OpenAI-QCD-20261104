import YM.Poised.Alumna
import YM.Poised.Polaris
/-! # Boost per coefficient. any tested moment vector in lifted orientation.
 Spend post-L but bounded polynomial (cone call). Derrick zeros.Port.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Tree RG Source Source.Drops MeasureTheory Finset WardBin Work.G05 Planned.PrimaryIntegral295 Planned.PrimaryIntegral295.Place
open scoped Topology BigOperators ContDiff Matrix.Norms.L2Operator TensorProduct Classical ComplexConjugate
open QCD QCD.Lat QCD.Grass UV Cylinder SourceRead
variable {B : Type}{d k j n:ℕ}{c l:Side}
namespace Chute
open Pipes QCD.Kit QCD.Flume QCD.Cove QCD.Creek QCD.Loom QCD.Flume QCD.Fork QCD.Port QCD.Brick Lining Lining.Ferry
open Precision Pressure Garden Run Laurent Carrier Next.Free QCD.Kit
open PhysicalNext.JointLoad Palette Steed Beacon MultiNext.SignedSource Cruising MultiNext.SignedSource.Lyre
open Display Kites PhysicalNext.Repeat PhysicalNext.Repeat.Brim
variable {K: KernelChoices}(P:Flight j k)(h:l.val=c.val*P.L.val)(T:Tube su (Flight.visit P K h)) (R:BudgetPoint)
variable {X:Support l}{Y:Support c}{b b':Cover} {u v L D' G₂ z M0 N:ℕ} {τ t vi vo a A C M Q0 ε:ℝ}
abbrev Λ (d:ℕ):= Fin (Fintype.card (ZBand d)+1)
lemma foundT (F:Alg (ZBand d)): F=∑ i:Λ d,mantel i.val F:=by
   let K:= ZBand d; apply Stew.poster; intro i; change _=coef i (∑ j:Λ d,Stew.panel j.val F); rw [map_sum]; simp_rw [Stew.angel]; have hp:i.card ≤ Fintype.card K:= card_le_univ _; let q:Λ d:= ⟨i.card,Nat.lt_succ_of_le hp⟩; rw [sum_eq_single q]; swap
   · intro j _ hj; rw [if_neg (by change q.val ≠ j.val; exact Fin.val_ne_of_ne hj.symm)]
   swap; ·simp
   rw [if_pos rfl]
-- unravel
variable (F:Grid l→Lat.Fields l 6)(H:TaperHol)(J:Labels.Jet su)(F₀:Grid c→ Lat.Fields c 6) (Vb:Hera.Rights su N)
lemma belongingT (U:Support c)(t:ℕ) : kite P h T (mantel t∘F) U= mantel t ∘ kite P h T F U:=funext fun i=> (Pika _ _ _).symm
variable (hn :n≤d)
include hn
lemma glazeG (p:ℕ)(hf:ContDiffAt ℝ d (F∘increment 1) 0): rayE d n t H b J (mantel p∘F)=mantel p (rayE d n t H b J F):=by
   obtain ⟨V,-,h⟩:= Beacon.obtainsD H b F hf; let v:=mantel (A:=ZBand d) p; let X:=engine t (ZBand d); unfold rayE; rw [← clm_step (X ∘_ ) n 0 _ v]; swap; · apply (X.toLinearMap.restrictScalars ℝ).toContinuousLinearMap.contDiff.contDiffAt.comp (f:=Beacon.moment _ _ _ _) (0:ℝ) ((h J).1.of_le (Nat.cast_le.mpr hn)) -- infer
   apply congr_arg (fun f=>iteratedDeriv n f 0); funext i; let A:=chain H.T (c:=l) b i d; let Q:= F (current H b d J i); change X (changeVars A (mantel p Q))=mantel p (X (changeVars A Q)); rw [← Pika,show mantel p (X _)=_ from Pika _ p _]; rfl
local notation "JT"=> t • J
local notation "U!"=> kite P h T F Y
local notation "Det"=> framesF (purseX (wrap l b) D' vi)
variable (hv: Flame F R X (wrap l b) vi D' z M)
variable (hz: Fintype.card (ZBand d)< z)(hN:d<N)(hP:N ≤ R.order)(hR:∀ i,Mom.needed X i→ Lyre.width R (wrap l b) i ≤ 1)(hs:0< vi)
variable (ht: ∀ i≤d, Venture (Pipes.purseX (wrap l b) D' vi) (fun _=>1) (P:=R) (o:=wrap l b) C (craftT d i (X:=X) (b:=b) (b':=b') P h T J vo t))(hx: ∀ i≤ d,Venture (Pipes.purseX (wrap l b) D' vi) (fun _=>1) (P:=R) (o:=wrap l b) ε (actionT d i (X:=X) (Y:=Y) (b':=b') P h T H J vo t - craftT d i (X:=X) (b:=b) (b':=b') P h T J vo t))(hC:1 ≤ C)(hε:ε≤ C)(hδ:0<ε)
def meritP (p n:ℕ)(Vb:Hera.Rights su N) (C:ℝ):ℝ:= Fintype.card (OrderedFinpartition n)*ult p Vb C
def fortuneP (d n:ℕ)(Vb:Hera.Rights su N)(C:ℝ) :=∑ i:Λ d, meritP i.val n Vb C
def cholate (d n:ℕ)(Vb:Hera.Rights su N)(ε C:ℝ):ℝ:= fortuneP d n Vb C*(2^N*ε)
omit hn in
lemma estuary (hn:1 ≤ C)(i:ℕ) :0 ≤ fortuneP d n Vb C:= Finset.sum_nonneg fun j _=> mul_nonneg (Nat.cast_nonneg _) (ult_pos hn _ _)
local notation "Fo"=> fortuneP d n Vb C
local notation "Ch"=> cholate d n Vb ε C
include hv hz hP hN hR hε hs ht hx hδ Vb hC
lemma dankT : ‖rayE d n vo H b' JT U!‖ ≤ (Ch+Fo)*M:=by
    let f₁(i:Λ d) := mantel i.val∘U!; have he :Healthy R.threshold X (1:Grid l) :=Next.Foundations.one_healthy _ _ R.threshold_pos.le; have hm:Fintype.card (ZBand d)+1≤ z:=hz; have ht0:ContDiffAt ℝ d (F∘increment 1) 0:= (hv.sight.use 1 he).of_le (Nat.cast_le.mpr (hN.le.trans hP)); rw [foundT (rayE d n vo H b' JT U!)]; simp_rw [←glazeG U! H JT hn _ (powered_germ P h T F ht0), ← belongingT]
    have h(i:Λ d):‖rayE d n vo H b' JT (kite P h T (mantel i.val ∘ F) Y)‖ ≤ (meritP i.val n Vb C*(2^N*ε) +meritP i.val n Vb C)*M:=by
        let Q:=mantel i.val ∘ F; obtain ⟨A,he,hK,hL⟩:=crewR F hv i.val
        have hp:= hv.issues _ (i.isLt.trans_le hm); have hX:=driftL P h T R J Vb H Q he A hR hL D' hp ht hx hC hε hδ hs hn hN hP
        let fW(p:ℕ):=craftT d p P h T (X:=X) (b:=b) (b':=b') J vo t
        let g(v:OrderedFinpartition n):=(iteratedFDeriv ℝ v.length (lotsF Q) 0) (fW ∘ v.partSize); let Z:=∑ v,g v; let a:=rayE d n vo H b' JT (kite P h T Q Y); have hg: ‖Z‖ ≤ meritP i.val n Vb C*M:=by apply (norm_sum_le ..).trans ((Finset.sum_le_sum fun j _=> up_cost (p:=i.val) P h T R J Vb Q he A hR hL _ hp ht hC hs hn hN hP j).trans_eq ?_); rw [sum_const,card_univ,nsmul_eq_mul]; unfold meritP; ring
        change ‖a‖≤ _; apply (le_trans (b:=‖a-Z‖+‖Z‖) _ ((add_le_add hX hg).trans_eq ?_)); swap; · unfold meritP; ring
        exact le_trans (le_of_eq (congr_arg norm (sub_add_cancel a Z).symm)) (norm_add_le ..)
    apply (norm_sum_le ..).trans ((Finset.sum_le_sum (fun i _=> h i)).trans_eq ?_); unfold cholate fortuneP; rw [←Finset.sum_mul,Finset.sum_add_distrib,Finset.sum_mul (s:=Finset.univ)]
variable (heT:T.R.A0=linesOf P a) (ha:0<a)(hk:4 ≤ k)(hΔ:d/2≤j)(hw:Nonwrapping X (wrap l b))(hL:100 ≤ l.val)(hg:∀ k U,slots 6 k (F (Lattice.gauge k U))=F U)
include heT ha hk hΔ hw hL hg
lemma cacheT (h0:∀ (J:Labels.Jet su)(k:ℕ), k<n→ WardBin.leading k (Beacon.moment (d:=d) H b J F)=0): ‖rayE d n vo H b' JT U!-(Kit.slope P.L)^n • rayE d n vo H b JT F‖ ≤ Ch*M:=by
    let f₁(i:Λ d) := mantel i.val∘U!; have he :Healthy R.threshold X (1:Grid l) :=Next.Foundations.one_healthy _ _ R.threshold_pos.le; have hm:Fintype.card (ZBand d)+1≤ z:=hz; have ht0:ContDiffAt ℝ d (F∘increment 1) 0:= (hv.sight.use 1 he).of_le (Nat.cast_le.mpr (hN.le.trans hP))
    have hx1(i:Λ d): ‖mantel i.val (rayE d n vo H b' JT U!-(Kit.slope P.L)^n • rayE d n vo H b JT F)‖≤ meritP i.val n Vb C*(2^N*ε)*M:=by
       let Q:=mantel i.val ∘ F; obtain ⟨A,hh,hK,hL'⟩:=crewR F hv i.val; have hp:= hv.issues _ (i.isLt.trans_le hm); have ht:= driftL P h T R J Vb H Q hh A hR hL' D' hp ht hx hC hε hδ hs hn hN hP; rw [map_sub,map_smul,← glazeG F H JT hn _ ht0,←glazeG U! H JT hn _ (powered_germ P h T F ht0),←belongingT]; apply le_trans (?_ : _ ≤ _) ((le_of_eq (show ((Fintype.card (OrderedFinpartition n):ℝ)* 2^N*ε*(ult i.val Vb C))*M=_ from by unfold meritP; ring)))
       let q:=(Kit.slope P.L)^n • iteratedDeriv n (engine vo (ZBand d) ∘ Beacon.moment H b (t • J) Q) 0
       have heq:= pricerT (b':=b') (vo:=vo) (t:=t) P h T H J Q A ((hh.smooth _ he).of_le (Nat.cast_le.mpr (hN.le.trans hP))) (inherent F hg i.val) hw hL heT ha hk hn (inherits b F H ht0 h0 i.val (by omega)) hΔ
       change ‖_- q‖≤ _; unfold q; rw [← heq]; exact ht
    rw [foundT (_-_)]; apply (norm_sum_le ..).trans ((sum_le_sum (fun i _=>hx1 i)).trans_eq ?_); unfold cholate fortuneP; rw [←sum_mul, ←sum_mul]
omit heT ha hk hΔ hw hL hg hv hz hP hN hR hε hs ht hx hδ Vb hC
-- truncate.Y.Output. Elementwise priceW beam.Y requires h+ faith. configure afterL.Up.include qualifier for n projections only. no k wisdom.
variable {n0 z0 m0 :ℕ}
omit hn -- remove
open Costs Display MassiveQCD.Plate
lemma verified (E Pk n d D':ℕ)(J:Labels.Jet su)(hn:n≤d): ∃ C:ℝ,0≤ C ∧ ∀ {j k c l} (P:Flight j k)(h:l.val=c.val*P.L.val)(K:KernelChoices)(T:Tube su (Flight.visit P K h))(R:BudgetPoint)(F:Grid l→Lat.Fields l 6)(Z:Grid c → Lat.Fields c 6)(Y:Support c)(o :Site c)(H:TaperHol)(b:Cover)(x D t:ℝ), LocalOn Y Z→ ContDiffAt ℝ d (Z∘increment 1) 0 → ContDiffAt ℝ d (F∘ increment 1) 0 → o ∈Y → coverNumber (radiusB x) Y ≤ radiusB x → separation o (wrap c b) ≤ E→R.threshold ≤ 2 * fiery su x P.L → R.power=Pk → surface d ≤D' → d*d ≤ R.power →0<t → 0≤D → (∀ j:Λ d,∀ i:ℕ,i≤d →∀ α:Directions su c,R.dirBound o α→ ‖α‖ ≤ canopyW su P.L R.power x → ‖leftDerivs (framesF (purseX o D' t)∘ mantel j.val ∘ Z) (List.replicate i α) 1-leftDerivs (framesF (purseX o D' t)∘ Fountain.cherub T (flareV (proton P h)) (mantel j.val ∘ F)) (List.replicate i α) 1‖ ≤ D) → ‖rayE d n t H b (R.threshold • J) Z - rayE d n t H b (R.threshold • J) (kite P h T F Y)‖ ≤ C*D:=by
    obtain ⟨C,hC,h⟩:= oracle d n E Pk D' J hn; refine ⟨(Fintype.card (Λ d):ℝ)*C,by positivity,?_⟩; intro j k c l P H K T R F Z Y o H' b x D t hZ hx hf hy ho hE hR hp hb hK ht hD hv; let J':= R.threshold • J
    rw [foundT (_-_)]; apply (norm_sum_le ..).trans ((Finset.sum_le_sum (g:=fun _=>C*D) (fun i _=>?_)).trans_eq (by rw [sum_const,card_univ,nsmul_eq_mul,mul_assoc]))
    rw [map_sub,← glazeG _ _ _ hn _ hx,← glazeG _ _ _ hn _ (powered_germ _ _ _ _ hf),← belongingT]; refine h c (mantel i.val ∘ Z) _ Y o H' b R P.L x D t (fun z j he=> congr_arg (mantel i.val (A:=Faces (Site c))) (hZ z j he)) ((mantel i.val).contDiff.contDiffAt.comp _ hx) ?_ hy ho hE hR hp hb hK ht hD (hv i)
    -- ContDiff.Fountain
    let f:= (mantel i.val)∘F; have hQ: ContDiffAt ℝ d (f ∘increment 1) 0:= (mantel (A:=Faces (Site l)) i.val).contDiff.contDiffAt.comp _ hf
    let L:=((changeVars (flareV (proton P H))).toLinearMap.restrictScalars ℝ).toContinuousLinearMap
    refine ContDiffAt.congr_of_eventuallyEq (L.contDiff.contDiffAt.comp (f:=(f∘increment 1)∘ Heir.route T) _ ?_) (Fountain.lofts _ _)
    exact ((map_zero (Heir.route T)).symm ▸ hQ).comp (f:=Heir.route T) (0:Directions su c) (Heir.route T).contDiff.contDiffAt
end Chute
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Chute.dankT
#print axioms YM.Massive.Poised.Chute.verified
