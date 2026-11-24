import YM.Poised.Cannon
import YM.Poised.Sheets
import YM.Poised.Drought
import YM.Poised.Looms
import YM.Poised.Transits
import YM.Poised.Pacific
import YM.Poised.Fountain
import YM.Poised.Street
import YM.QCD.Fawn.Price
/-!
# Charter interior, picks real Crown.
Shrink discharged D.ε at furnishing before actual x height. Allows full-rank path cost with constant output.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Poised
open Function Filter Set Lattice Wilson Pressure RG Precision Tree Next Next.SectorChange Next.Fluctuations Next.Foundations
    Exterior Bloch Bid Push.SectorMeasure MultiNext.SignedSource MultiNext.SignedSource.Banjo Planned.AtomRegular MeasureTheory Analysis
open AnalyticBridge.SectorAffine.Offset WardBin.Lies PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open QCD QCD.Lat QCD.Kit QCD.Grass QCD.Brick QCD.Cove QCD.Stew ConnectedActivityE6.Blaze Push.Uniform UV Cylinder SourceRead
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {B :Type}[Fintype B] {c f : Side} {S : StepData c f} {T : Tube su S} {Pt : Teller su} {k : S.Choices} {V : Config su c} {F : Forest S.ratio}
    {P R : BudgetPoint} {o : Site f} {g : Site c → su.El} {X : Support f} {Y : Support c} {Q M m r t x τ W w σ G₀ ρ v s u u₁ u₂: ℝ} {I : Type} {J: BudgetPoint}
    {A : Stores S} {n l N j q₀ : ℕ} {D : Slab su c l} {q : Chi} {d : ℝ} {V' : Config su f → Lat.Fields f 6}
namespace Fountain
open Pipes
local notation "Y'"=> Fields f 6 -- remove amb
variable (a:Museum F x A X Y I)[Fintype I] {C: Libretto su n}{E: Heir.Record}
variable (hp:Plays C E P R Pt T x) (b:Cover) (hw:wrap f b∈X) (hg :Canvas P (S.ratio.parent (wrap f b)) (reach x) V g n C.C)
variable (hO:Short S R X)(hn:2≤n)(hV: Healthy P.threshold Y V) (U:Grid f)(z: Prices su I)(hu:0≤u) (hv:u*‖tape z‖≤ E.ε*R.threshold)(hl:l≤n) (hD:∀ i,P.dirBound (S.ratio.parent (wrap f b)) (D i))
set_option quotPrecheck false
local notation "O"=> S.ratio.parent (wrap f b)
local notation "X₀"=> enters V (S.ratio.parent (wrap f b)) (reach x) g D (a.extra g u z)
local notation "Z₀"=> launch V (S.ratio.parent (wrap f b)) (reach x) g D
local notation "V₀"=> Heir.loom P (reach x) C.C
local notation "b'"=> Kit.slope S.patch.L
variable {p p₀ :ℕ}{I₀ I₂ χw R₁ :ℝ}
open PhysicalNext.Repeat Cub
-- ,g=1 even no Short; agreement common chart at identity.
variable [DecidableEq I](α: Directions su c)
local notation "F⚬"=> (1:Frame c)
local notation "V⚬"=> (1:Grid c)
local notation "qe"=> a.extra F⚬ u z
open MultiNext.SignedSource MultiNext.SignedSource.Lyre
variable (N Yp:ℝ)(hA:‖α‖ ≤ N*loom P (reach x) C.C) (hN:1 ≤ N)
local notation "An"=> Heir.loom P (reach x) C.C
local notation "D0"=> fun s:ℝ=> (rod α s,a.extra (1:Frame c) u z)
local notation "v0"=> route T ∘ rod α
local notation "m0"=> u*‖tape z‖
local notation "ψ₁"=> ((E).Q)
variable (i:ℕ) (w:B→ℝ)(U':VectorD (Site f) B)(fw A₀:ℝ) (hq:SeatD (purseX (wrap f b) i fw) w U' Yp) (hYp:1 ≤Yp)
local notation "Y₂"=> purseX (wrap f b) i fw
variable (ht:∀ i,w i>0)(hf:fw>0)(hκ:∀ i j:Pipes.Shell,∀ x:su.Color,‖x‖≤1→ Through n (yaw i j) x A₀)(hM:C.M*(N*loom P (reach x) C.C) ≤1)
variable (W:ℝ) (hW:0 ≤ W) (hqW: clinicFee n E.Q*loom P (reach x) C.C ^2 * N^n + u*‖tape z‖≤ W*R.threshold) (hΨ: (1+patterns n)*(A₀*(C.M*(N*loom P (reach x) C.C)))*((Fintype.card Pipes.Shell:ℝ)*Yp) ≤ W)
-- comparator.Quasi.P. `mouth` constant needs path.S seat at **Yp constant**! H 0=0? φ(y=0)=0 so y.2−...=0. use exact.
variable (f':Grid f→Lat.Fields f 6)(nf:ℕ)
set_option quotPrecheck false
local notation "s0"=> quakes T α U'
local notation "s'"=> shiver T F x k α qe U'
local notation "Xt"=> (framesF w∘lotsF f')
variable (hG : ∀ k U,slots 6 k (f' (Lattice.gauge k U))=f' U) (heV:Ease.Charm R X f') (hS:∀ V,f' V∈ Creek.region (limits X)) (hB:∀ V,f' V ∈ layer (Faces (Site f)) nf)
variable (hh:R.supBounds (wrap f b) X (framesF (purseX (wrap f b) i fw)∘f') τ)(Vb:Hera.Rights su n)
variable (hhA:Sized Yp (route T α) R (wrap f b))(hLi:∀ i,Mom.needed X i→ width R (wrap f b) i ≤1)
local notation "Kⁱ"=>framesF w ∘ cherub T U' f'
variable (L:Alg B→L[ℝ]ℝ)(hlL:‖L‖ ≤1) (χ:Chi)
open AnalyticBridge.LocalGaussian.Moments Heir.Lute Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score AnalyticBridge.LocalGaussianLaws Heir.Carillon
-- first.Clue input chart actual.
local notation "Rz"=>Pipes.mouth (1+n+Yp) Vb n nf
local notation "θ!"=> guard χ su I u (E.ε*R.threshold)
local notation "gq"=> fun A:Grid f=> framesF w (changeVars U' (f' A))
local notation "Vq"=> fun V:Grid c=>gq (a.received k T q d u V U z)
local notation "ve"=> L ∘ (gq)
variable (hd:P.dirBound (S.ratio.parent (wrap f b)) α) {rm m₃ :ℕ}
local notation "αΓ"=> fun v=> v=α
variable (hW': 0<W)(h0:W≤1) (hts:Walled S X Y x rm)
-- in cost W normalized z.Seat pledge from opal * etc.
local notation "Oz"=> (opal C E P R S.patch.L X rm x u)
local notation "vt"=> R.threshold*Carillon.pitch n _ E.Z (Heir.scope R X rm x) P.power z
local notation "H"=>powers z ^ 2
local notation "γ"=> Carillon.speed n E.Z R.threshold P.power (Heir.scope R X rm x) z
variable (hhOz: opal C E P R S.patch.L X rm x u *N^n ≤ W)
local notation "T'"=> patterns n*(1+(2:ℝ)^n)*(Yp+1)^n * Rz
local notation "Tq"=> patterns n*(Yp^n*Rz*τ)
local notation "D!"=> T' * (W*H^(n+1))*τ
include hW' hN hhOz hp hM hf ht hlL hA hq hκ hΨ hYp hhA hd hLi h0 hts χ hh hB Vb

variable (huP:0<u)(hhx :m₃<n) -- name
include hG hw huP
include U hn hp heV
noncomputable abbrev sheen (nf :ℕ) (Vb:Hera.Rights su n)(W Yp:ℝ):= (patterns n*(1+(2:ℝ)^n)*(Yp+1)^n*Pipes.mouth (1+n+Yp) Vb n nf*W+2*W*(patterns n*(Yp^n*Pipes.mouth (1+n+Yp) Vb n nf)))*((n:ℝ)*4+1)^n
local notation "Z0"=> opal C E P R S.patch.L X rm x u
local notation "m₀"=> 2*((n+1)+(n+1))
set_option maxHeartbeats 360000 in
lemma bark (Z : Prices su I) (j:ℕ)(hm:j<n): let b:= a.concert T u q d k ve θ! U 1 Z; let p:= List.replicate j α; let A:= Complex.ofRealCLM ∘ L ∘ Kⁱ
    ‖leftDerivs b p 1-leftDerivs A p 1‖ ≤ sheen nf Vb W Yp * τ*powers Z^m₀:=by
    intro Z' p0 V'
    let A:= Complex.ofRealCLM ∘ L ∘ Kⁱ; let H':=powers Z ^2; have hg: 1 ≤ H':=one_le_pow₀ (grows Z); have hK : Band j αΓ V⚬ (Carillon.speed n E.Z R.threshold P.power (Heir.scope R X rm x) Z+1) _ (Z'-A):= rich (k:=k) a hp b hw hn U Z α N Yp hA hN i w U' fw A₀ hq hYp ht hf hκ hM W hΨ f' nf hG heV hB hh Vb hhA hLi L hlL χ hd hW' h0 hts hhOz huP hm -- explicit
    let p:ℝ:=(n:ℝ)*4+1; have hp':1 ≤ p:=by unfold p; have h: 0≤ (n:ℝ):=Nat.cast_nonneg _; linarith
    have hx: R.threshold*pitch n _ E.Z (Heir.scope R X rm x) P.power Z ≤ H':=by
         have hr0:= Cub.tide (D:=E) (P:=P) (B:=R) a hts hw Z (by omega:1 ≤ n); have h : Oz ≤ 1:= ((le_mul_of_one_le_right (opal_nn _ _ _ _ _ _ _ _ _ huP.le) (one_le_pow₀ hN)).trans hhOz).trans h0
         have hx: scratch (n:=n) su E P R S.patch.L X rm x ≤ 1 := by
          refine le_trans ?_ h; apply le_trans _ (show Lute.rust C E P R _ _ _ _ _ ≤ Oz from le_add_of_nonneg_right (by have hQ:= E.guards; unfold ζ; have hr:=R.threshold_pos; positivity)); unfold rust; exact le_add_of_nonneg_left (add_nonneg (segment_nn n X P R E.majorant C.matins) (tranche_nn _ _ (zero_le_one.trans E.majorant) huP.le R.threshold_pos.le))
         exact hr0.trans (mul_le_of_le_one_left (sq_nonneg _) hx)
    let Y:= V'; have hY: Multi.Puff.Crest j A 1 :=by
       have hf0:Push.Local.Chart n Kⁱ 1:= (framesF w).contDiff.contDiffAt.comp _ (nest (T:=T) U' f' heV hp.rehearsed.orders)
       have h: WardBin.Lies.Germ n A 1:= Complex.ofRealCLM.contDiff.contDiffAt.comp _ (L.contDiff.contDiffAt.comp _ hf0); exact into j A (h.prod hm.le)
    let D:= T' * (W*H'^(n+1)) *τ+(W*H')*Tq+(W*H')*Tq
    have hb : Multi.Puff.Crest j Z' 1:= (sub_add_cancel Z' A) ▸ into _ _ (hK.readable.germ.add hY.germ) -- include notation
    have ht0:= hK.caps p0 (by simp [p0]) (fun x hx=> (List.eq_of_mem_replicate hx)); rw [Cub.redacted hb hY (by simp [p0])] at ht0
    unfold p0 at ht0; rw [List.length_replicate] at ht0; apply ht0.trans
    let γ':= Carillon.speed n E.Z R.threshold P.power (Heir.scope R X rm x) Z; have hr:γ'+1 ≤ p*H':= by unfold γ' Carillon.speed p; nlinarith only [mul_le_mul_of_nonneg_left hx (Nat.cast_nonneg (α:=ℝ) n),mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α:=ℝ) n),hg]
    have hq': 0 ≤ D:=hK.nonneg; have hV:0≤ Rz:=by unfold Pipes.mouth; have h:=Vb.large; positivity
    have hz:=hh.1; let T0:= sheen nf Vb W Yp*τ; have hT : 0 ≤ T0:=by unfold T0 sheen; positivity [patterns_nonneg n]
    change D * (γ'+1)^_ ≤ _
    apply (mul_le_mul_of_nonneg_left ((pow_le_pow_left₀ hK.sane hr j).trans (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hp' hg) hm.le)) hq').trans
    have hf: (W*H')*Tq ≤ (W*H'^(n+1))*Tq:=by
       have hp:= le_self_pow₀ hg (Nat.succ_ne_zero n); have hh:0≤ Tq:=by positivity [patterns_nonneg n]
       exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hW'.le) hh
    apply (mul_le_mul_of_nonneg_right (add_le_add (add_le_add (le_refl _) hf) hf) (show 0 ≤ (p*H')^n by positivity)).trans
    calc
       _=T0*H'^(n+1+n):=by rw [pow_add H' (n+1) n,mul_pow p]; unfold T0 sheen p; ring -- edit
       _≤_:=mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hg (by omega : n+1+n ≤ (n+1)+(n+1))).trans_eq (pow_mul _ 2 _).symm) hT -- order
-- buy Exchange smooth at 1. coarse any.I. need cost Input sup of scalar from load.
variable {xτ:ℝ} (hX:R.supBounds (wrap f b) X (L ∘ (fun A:Grid f=> framesF w (changeVars U' (f' A)))) xτ)
include hX
lemma blanket (j:ℕ)(hl:j<n): let l:= List.replicate j α; let h:= a.hymn T u q d k ve θ! U
    Multi.Puff.Crest n h 1 ∧
    ‖leftDerivs h l 1 - leftDerivs (L ∘ Kⁱ) l 1‖ ≤ sheen nf Vb W Yp*τ * AnalyticBridge.LocalGaussian.Moments.meter (heads su R S.patch.L X rm x) 0 E.K (2*((n+1)+(n+1))) := by
    intro l h; let v00:= V⚬; let μ:=Gaussian.cloud (a.twilight k T v00); let Z(z):=a.concert T u q d k ve θ! U 1 z; let V:= Complex.ofRealCLM ∘ L ∘ Kⁱ; let f₁(z:Prices su I):= leftDerivs (Z z) l 1; let z' :=leftDerivs V l v00; let H':= sheen nf Vb W Yp*τ
    have he:Germ n (L∘Kⁱ) V⚬:= L.contDiff.contDiffAt.comp _ ((framesF w).contDiff.contDiffAt.comp _ (nest (T:=T) U' f' heV hp.rehearsed.orders)); have hj:l.length≤n:=by simp [l,hl.le]
    have ht: Healthy P.threshold Y v00:=one_healthy _ _ P.threshold_pos.le; have h':=hp.cantos (k:=k) a ht hts hw; have hθ : Silences su I n u (E.ε*R.threshold) θ!:=guard_silent χ huP (mul_pos E.guards R.threshold_pos)
    have hv : Ease.Charm R X ve:=heV.scales (L.comp ((framesF w).comp (Fountain.vat U')))
    have hv':=Hera.guise Vb a U hv hX hw hp ht huP.le θ! hθ k q d rm
    have hGv :0 ≤ Hera.grandFee Vb*xτ:=by unfold Hera.grandFee; have h:=Vb.large; have hp:=hX.1; positivity [patterns_nonneg n]
    obtain ⟨g1,g2,g3⟩:= Hera.exchange (k:=k) a U hp hw hGv hts huP.le hθ ht hv' l hj
    have hZ: ‖z'‖≥0:= norm_nonneg _; refine ⟨g1,?_⟩
    rw [← Complex.norm_real,Complex.ofReal_sub,show ((leftDerivs h l 1:ℝ):ℂ)=∫ z,f₁ z ∂μ from g3,show ((leftDerivs _ l 1:ℝ):ℂ)= z' from (Push.Local.left_linear Complex.ofRealCLM l (show Push.Local.Chart n (L∘Kⁱ) 1 from he) hj).symm,show (∫ z,f₁ z ∂μ)-z'=∫ z,f₁ z-z' ∂μ from by rw [integral_sub g2 (integrable_const _),integral_const,MeasureTheory.probReal_univ,one_smul]]
    obtain ⟨hQ,hY'⟩:= purchased ∅ (zero_lt_one.trans_le E.peak) h'.pos h'.peak m₀; change MeasureTheory.Integrable (fun z=> slopeEnvelope ∅ E.K m₀ z) _ at hQ; simp only [slopeEnvelope,AnalyticBridge.LocalGaussian.Moments.load,Finset.sum_empty,mul_zero,Real.exp_zero,mul_one,Finset.card_empty] at hQ hY'
    have hb : (∫ z,powers z^m₀ ∂μ) ≤ AnalyticBridge.LocalGaussian.Moments.meter (heads su R S.patch.L X rm x) 0 E.K m₀:= by apply hY'.trans; unfold AnalyticBridge.LocalGaussian.Moments.meter; have hx:=a.viewed hts R hw su; have hV:=E.peak; have hK:=inflate_ge m₀ (by positivity : 0 ≤ E.K⁻¹/8); gcongr <;> exact hx
    refine (norm_integral_le_integral_norm ..).trans ((integral_mono ((g2.sub (integrable_const z')).norm) (hQ.const_mul H') (fun z=> bark (k:=k) a hp b hw hn U α N Yp hA hN i w U' fw A₀ hq hYp (by assumption) hf hκ hM W hΨ f' nf hG heV hB hh Vb hhA hLi L hlL χ hd hW' h0 hts hhOz huP z j hl)).trans ?_); rw [integral_const_mul]; apply mul_le_mul_of_nonneg_left hb; unfold H' sheen Pipes.mouth; have hp:=hh.1; have hv:=Vb.large; positivity [patterns_nonneg n]
end Fountain
end YM.Massive.Poised
#print axioms YM.Massive.Poised.Fountain.blanket
