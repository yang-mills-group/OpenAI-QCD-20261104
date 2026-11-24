import YM.Massive.Kindred.Studio
/-! # Work towards trajectory pressure under Mark: L1 majorants -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Acre
open Function Lattice RG Laurent Bloch Matrix Metric Precision Wilson Bid Craft Exterior Filter
open YM.Next.Free YM.Work YM.Further.PhysicalPeriodLimitF933
open WilsonStartup Design Change Extra.Iteration Stationary Tree Raft Garden Transfer Orbit Sparks Fog Birth Raft.ParcelR
open ConnectedActivityE6 Pressure Pressure.Stores
open Push Push.AbsoluteSums Exterior Shell Stationary Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid SliceRows Mask Coat
open Census Green Mask Pulse Itinerary Presented LabelSum Matter Poll Pond Packets
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical
open PhysicalNext.Repeat Slide PulseRide
open Deck Moss Calm World World.Alley Villa Flume Jets Kit Bay Leaf Tee Run Port Pine Stem Coda Finch Kites Reggae Loom Loom.Fleet Cove Lat
open QCD.Beam Jets.Touch Patron Stem
open Fork GasP Push.Uniform PhysicalNext.Repeat.Song AnalyticBridge.VerifiedReset Time
open scoped PhysicalNext.Repeat.Greenbelt
variable {c f C F L:Side} {J:Patch} {j k n m i l N n' :ℕ}{a A d D Y M w x μ q ν η α γ ρ σ η₀ δ ζ H z v u w₀ w₁ w₂ W:ℝ}
variable {P: BudgetPoint}{G:Stage}{T': Teller su}{Q:ConnectedActivityE6.Target su T'}{o:Target.Order su W}
open Stew Ursell
variable {S:Flight j j}{K:KernelChoices}{h:f.val=c.val*S.L.val}{R:BudgetPoint}{T:Tube su (S.visit K h)}
variable {X:World P G x n' i k a A d D Y M w S.L.val}
variable {I J' : Type}
open Blaze Shells Sands Dust King -- edit
open Lapis Sienna Fare Octave Fount Grove
open Planned.JetPort Tidings Entr
open PhysicalNext.JointLoad Heir Warmlet
open Footprint Push.Local Shard DoorKit Badge Adornment
open scoped PhysicalNext.Repeat.Greenbelt
namespace Rails
variable {Ω:ParcelR} {χ:Chi}{s₀ β β' r ν' b A' W' κ v₀ y ε Λ:ℝ} {U V:SunR Ω} (P₀:Plan j) {τ:Policy Q T'.top N}
open Grass


open Grass Patron
variable (A: Voice f N) (i₀:Flavor N) (T) (B: Badge P₀ τ R P o χ T U b (run S.L x) r β μ z)


local notation "δ'"=> α+(N:ℝ)*ν
open Struck Library Weft Fibre
namespace Reference
-- one-step transfer along same stopping parameters. No growth frame of F along unchosen schemes.
variable {A3 tol:ℝ}{E:ℕ→SunR Ω}{Xb:ℕ→ℝ}{Ut:ℕ→Towers J.L}
variable (F₀:Flavor N)(M₀:Arrow N) (B:SparkMesh) {M':ℕ→ SparkMesh} (g:PulseRide T'.bind T'.top.clip J a d M' n) (hΓ:PassageX τ D B M' F₀ χ g Ω E Xb Ut x κ s₀ 1 μ z 1 W' H A' (1/8) o A3 tol)
set_option quotPrecheck false
local notation "f₁"=> towerQ J B n i k
local notation "c₁"=> towerQ J B n (i+1) k
variable {t:ℝ}{Δ:PlaqAxes} {V1 U1 W1:ℕ→ℝ}{Pt:ℕ→BudgetPoint}{D0 a3 Q₀ ξ:ℝ}{Q1:∀ j,Pixel (towerQ J B n j k) N}
-- implicit tol not from above? A3 variables namespace shadow from Bank; outside ended.Bank need declare. see compile.
local notation "xg"=> delay J n i x
local notation "xo"=> delay J n (i+1) x
open Conductor Conductor.Quant High Meridians Ruby High.PrismT Massive.Filament
variable (hZ: Moor t T' B F₀ g Pt E (fun i=> g.costP i+N*Xb i) κ x τ.t D W' k V1 U1 W1 Q1 Δ s₀ tol)
variable (F:∀ j,ℂ→Pixel (towerQ J B n j k) N)
open Aperture Conductor.Quant
open Kin Sway OrbitG MeasureTheory NormedSpace
variable (G₀: Gem c N I)(T: Patron.Rail c N J')
open Finset
namespace Sharp
abbrev area (c:Side): ℝ:= Fintype.card (Site c)
local notation "uZ"=> (fan L η x)
local notation "νT"=> (1/8:ℝ)
lemma model (h: Licence P q w t G₀)(V:Grid c)(hv:0≤ q)(ht:1≤t): ‖Patron.total G₀ P.threshold V‖ ≤ area c*w:=by
   obtain ⟨p,hp,hX⟩:= h.zone; let f i:= letters G₀ P.threshold V i; have hK(i):0 ≤p i:=(hX i).travel; have hh(i): ‖f i‖ ≤ p i:=by
      by_cases hv : Healthy P.threshold (G₀.addr i).support V; swap; · unfold f letters; rw [masked_ne _ _ _ _ hv,norm_zero]; exact hK _
      unfold f letters; rw [masked_eq _ _ _ _ hv]; exact (Loom.tore _ ht).trans ((Stew.shot (Stew.lens (G₀.addr i).site) _ _ (zero_lt_one.trans_le ht)).trans ((hX i).sizeU V hv))
   have hQ:= budget_mono (Stem.mast G₀ p hp hK hv) (fun i=>norm_nonneg _) hh; exact (norm_tsum_le_tsum_norm hQ.2.1).trans hQ.2.2
lemma nighLight (p:Finset J')(X:J'→ EvenA c N): ‖∏ i∈p,X i‖ ≤ ∏ i∈p,‖X i‖:=Finset.norm_prod_le ..
lemma mini (V:Grid c) (h: Quits T P.B w u v t) (hu:1≤u)(hv:0≤v)(ht:1≤t): ‖heartK T P.threshold V‖ ≤ Real.exp (area c*w):=by
    obtain ⟨p,hp,hX⟩:=h.cost; have hg i:0 ≤ p i:=(norm_nonneg _).trans (hX i 1); have he (i): p i ≤ taxed (oriD T) p u i:= le_mul_of_one_le_left (hg i) (one_le_pow₀ hu); have hh:=spiritual (c:=c) (taxed (oriD T) p u) (Ruby.home T) hp (fun i=>(T.addr i).alive.mono (T.addr i).part) hv (fun i=> (hg i).trans (he i))
    have hE:= Rails.sunpow (budget_mono hh hg he); let f:=Ruby.tK T P.threshold V; have hf(i:Finset J'): ‖f i‖≤ ∏ j∈i,p j:=by
       unfold f tK; split; · exact (nighLight _ _).trans (prod_le_prod (fun _ _=>norm_nonneg _) fun j _=> (Loom.tore _ ht).trans (hX j V))
       rw [norm_zero]; exact prod_nonneg (fun i _=> hg i)
    have hz:=budget_mono hE (fun i=> norm_nonneg _) hf; exact (norm_tsum_le_tsum_norm hz.2.1).trans hz.2.2
-- from Ladder μ.He compact prices u≤1+ C. schedule
abbrev outE (N:ℕ)(ε D:ℝ):ℝ:=1+(Struck.Library.Carrier.Rental N*ε+ D*ε*2)
abbrev outK (D ε:ℝ):ℝ:= 1+(D*ε+D*ε)
lemma underpriced (Y:Code c N)(A:Arrow N)(h:0≤v)(hp:∀ i,|t^2*Y.focus i-v*A.tip i|≤ v/2): Library.wage Y t ≤ Library.Carrier.Rental N*v:=by
   have hv i:t^2*‖Y.focus i‖≤6*v:=by
       have he := (abs_le.mp (hp i)); have ht:= abs_le.mp ((abs_mul v (A.tip i)).trans_le (mul_le_mul_of_nonneg_left (A.bound i) (abs_nonneg v))); rw [abs_of_nonneg h] at ht; rw [Real.norm_eq_abs,← abs_of_nonneg (sq_nonneg t), ← abs_mul]; apply abs_le.mpr; constructor <;> linarith only [he.1,he.2,ht.1,ht.2,h]
   unfold Library.wage Struck.Library.Carrier.Rental; apply le_trans (mul_le_mul_of_nonneg_left (sum_le_sum (fun i _=> (mul_le_mul_of_nonneg_left (hv i) (Pith.priceP_nonneg)))) (Real.exp_pos _).le); apply le_of_eq; simp only [Finset.sum_const,card_univ,nsmul_eq_mul];ring
namespace Price
local notation "χ₁"=> Jets.Touch.chip L x
-- Earned inputs.No angle small yet.
lemma fitting (Y:Code c N) (A:Arrow N)(hr:P.B=highR L x)(he:Desk Y P i₀ L x η)(hp:∀ i,|(fan L η x)^2*Y.focus i-w*A.tip i|≤ w/2)(hq:0≤ D) (ht:0 ≤ v)(hv: v≤1)(h:0≤ ε)(hM:w=Quant.crest L x ε v)(hA:Struck.Library.Fare Y P L x η (D*w) (v*D*w))(hX:0≤χ₁)(hy:χ₁≤1)(z:ℂ)(hz:‖z‖≤1) : Cheap (Y.EvalE z) (Y.EvalK z) P L x η (outE N ε D*χ₁) (outK D ε) :=by
   have hc:0 ≤ ε*χ₁:= mul_nonneg h hX; have hm:0≤w:= hM.symm ▸ (mul_nonneg (sq_nonneg v) hc); have hh:(D*w)+(v*D*w) ≤ (D*ε+D*ε)*χ₁:=by
        have hg:w≤ε*χ₁:= hM.trans_le (mul_le_of_le_one_left hc (pow_le_one₀ ht hv)); nlinarith only [mul_le_mul_of_nonneg_right hv (mul_nonneg hq hm), mul_le_mul_of_nonneg_left hg hq]
   obtain ⟨hE₁,hK₁⟩ := materCost Y hr he hA z hz; constructor; swap
   · exact wattsLoosen _ hK₁ (add_le_add_right (hh.trans (mul_le_of_le_one_right (by positivity) hy)) _)
   obtain ⟨f,hf,hK⟩:= hE₁.zone; have hw :w ≤ ε*χ₁:= hM.trans_le (mul_le_of_le_one_left hc (pow_le_one₀ ht hv)); have h:= (underpriced Y A hm hp).trans (mul_le_mul_of_nonneg_left hw (Bank.Nimbus.forest N)); refine ⟨f,fun i=> budget_loosen (hf i) ?_,hK⟩; unfold outE; nlinarith only [h,hh]
open Next.Rank IV Rain
section price
-- d,Λ invoice bound; nonpositive d/Λ implies absurd from path. could abs-max.
variable (P : Plan j) (T : Teller su) (L : Side) (Ω : ParcelR) (a d Λ κ η : ℝ)
variable (historyT : Ω.Rates σ)
include historyT
theorem procMeter (hη : 0 < η) (hκ : 0 < κ) (Z Q:ℝ): ∃ K:ℝ,
    ∀ᶠ x in atTop, ∀ (c : Side) (p : BudgetPoint), Now L p T.top x → ∀ (F:Voice c N),
    Struck.Library.Cheap F.P F.K p L x η Z Q → ∀ (V : Grid c) (v : Train j) (S : SunR Ω) (D : PathData su),
    D.Bounds T.top.clip a d Λ → ∀ β m:ℝ, run L x/2 ≤ β → β ≤ 2*run L x → |m|≤roofK L η κ x →
    ‖red F.P F.K S P v p D T.top.clip (haloK L x) β m 0 V‖ ≤
      YM.Massive.Pressure.major su c K (2*gaugeSize L x/strength T.top.clip) V:=by
   obtain ⟨M,hM⟩:= Globe.uniformVeil P Ω historyT 1
   let e := 2^2 * (Smoke.expPrice 2 Ω.t*Ω.e)
   let W := Globe.bPeak M N + (↑N*e + 4*d + Λ + Fintype.card PlaqAxes)
   refine ⟨W+Z+Q,?_⟩
   filter_upwards [Reference.prices T.top L η κ hκ hη] with x hx c p hp F hF V v S D hD β m hβ hB hm
   obtain ⟨h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,t⟩:= hx
   let A := scent S.Z.page p D T.top.clip β 0 N V
   let D' := FieldB Ω S c (haloK L x) P v + m • 1
   let X : EvenA c N := nozzle c N (D' V); let Y:= Patron.total F.P p.threshold V
   have ht:= (t p hp); let l : ℝ := Fintype.card (Site c); let O:= (2*gaugeSize L x/strength T.top.clip)
   let R:=∑ u:Face (Per c), su.chord (faceValue V u)/O; have hd :0≤d:=Push.AbsoluteSums.budget_nonneg hD.three; have hD':0 ≤ Λ :=Push.AbsoluteSums.budget_nonneg hD.two
   have ha : A ≤ l * ((N:ℝ)*e+4*d+Λ+Fintype.card PlaqAxes)-R:=by
          have hm:= YM.Massive.Pressure.exponent_retains hD (show (0:ℝ)<2*gaugeSize L x by positivity) ht.1 (ht.2 β hβ hB).1 V
          have hq := (abs_le.mp (Rain.second id 2 S.Z.page (S.Z.cost historyT.ht) historyT.ht V)).1
          have hn := mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg N (α:=ℝ)); change R- l* _ ≤ _ at hm; change ↑N * -(l*e) ≤ _ at hn
          unfold A scent Reggae.pulse; have hu : l*PathData.loopsPrice p β d Λ ≤ l*(4*d+Λ):= mul_le_mul_of_nonneg_left ((ht.2 β hβ hB).2 d Λ hd hD') (Nat.cast_nonneg _)
          linarith only [hm,hn,hu]
   have hu : ‖X‖ ≤ l*Globe.bPeak M N:= Globe.engineR N (D' V) (hM v c S m (hm.trans h7) _ h10 h11 V)
   have hU : 1≤taxK L x 1:=Real.one_le_exp (mul_nonneg zero_le_one (fan_pos ..).le)
   let K0 := heartK F.K p.threshold V
   have hL:‖K0‖ ≤ Real.exp (l*Q):=mini (T:=F.K) V hF.bill hU (by norm_num) h8
   have hy:‖Y‖ ≤ l * Z:=Sharp.model F.P hF.shelf V (by norm_num) h8
   have hxy : ‖exp (X+Y)‖ ≤ Real.exp (l*(Globe.bPeak M N)+l*Z):=by
          linarith [(norm_sub_norm_le (exp (X+Y)) (1:EvenA c N)).trans (stipend _ ((norm_add_le X Y).trans (add_le_add hu hy))), show ‖(1:EvenA c N)‖=1 from norm_one]
   change ‖exp (baker c N A+X+Y)*K0‖ ≤ Real.exp (l*(W+Z+Q)-R)
   rw [add_assoc,censor, smul_mul_assoc, norm_smul,Real.norm_of_nonneg (Real.exp_pos _).le]
   refine (mul_le_mul (Real.exp_le_exp.mpr ha) ((norm_mul_le ..).trans (mul_le_mul hxy hL (norm_nonneg _) (Real.exp_pos _).le)) (norm_nonneg _) (Real.exp_pos _).le).trans_eq ?_
   rw [←Real.exp_add,← Real.exp_add]; apply congr_arg; unfold W; ring
end price
-- convert Voice unmark comparison. origin.Z equivalence c0^_LL ≤ z_Reg* exp 2l.
variable (V W:Voice c N)(v:Grid c→ℝ)(S:St c)
lemma bands (hv:v 1=0)(h:Enn P i₀ L x η νT (duo V.P V.K))(hp:P.B=highR L x)(ht:1≤ uZ)(hh:χ₁ ≤ 1):
   Real.exp (-area c) ≤ ‖mud (scoreV V.P V.K P.threshold v S 1)‖∧ ‖mud (scoreV V.P V.K P.threshold v S 1)‖≤Real.exp (area c):=by
   rw [flatP V S v,hv,zero_add]; let K:=Patron.total V.P P.threshold 1; let l:= area c;
   have hM: 0 ≤ l:= Nat.cast_nonneg _; have hf:= Library.steady V h hp; have hx: ‖K‖≤ l:= (Sharp.model _ hf.shelf (1:Grid c) (by norm_num) ht).trans (mul_le_of_le_one_right hM hh); obtain ⟨hp,hF⟩:= abs_le.mp ((Complex.abs_re_le_norm (mud K)).trans ((mud_pay _).trans hx)); exact ⟨Real.exp_le_exp.mpr hp,Real.exp_le_exp.mpr hF⟩
local notation "Xr"=>Grid c
lemma haloPos (hv:v 1=0)(h:Enn P i₀ L x η νT (duo V.P V.K))(h2:Enn P i₀ L x η νT (duo W.P W.K))(hp:P.B=highR L x)(ht:1≤ uZ)(hh:χ₁ ≤1)(Z:ℝ)(β:ℂ)(hs:0<Z) (hSX:Z • scoreV V.P V.K P.threshold v S=β • scoreV W.P W.K P.threshold v S) : ‖β‖ * Globe.expo 2 c ≤ Z:=by
   let X:=scoreV V.P V.K P.threshold v S (1:Xr); let Y:= scoreV W.P W.K P.threshold v S (1:Xr); have he: ‖mud ((Z:ℂ) • X)‖=‖mud (β • Y)‖:= congr_arg (fun x:EvenA c N=> ‖mud x‖) (congr_fun hSX 1)
   have hg(x:EvenA c N)(v:ℂ): ‖mud (v • x)‖=‖v‖*‖mud x‖:=by rw [show mud (v• x)= _ from (map_smul (clay c N) v x),norm_smul]; rfl
   rw [hg,hg,normS Z hs.le] at he; let l:=area c; have hf : ‖β‖*Real.exp (-l) ≤ Z * Real.exp l:=le_trans ((mul_le_mul_of_nonneg_left (bands i₀ W v S hv h2 hp ht hh).1 (norm_nonneg β)).trans_eq he.symm) (mul_le_mul_of_nonneg_left (bands i₀ V v S hv h hp ht hh).2 hs.le)
   apply le_of_mul_le_mul_right (a:=Real.exp l) ?_ (Real.exp_pos _); refine le_trans (le_of_eq ?_) hf; rw [mul_assoc,Globe.expo,← Real.exp_add]; unfold l area; ring_nf
end Price
end Sharp
end Reference
end Rails
end YM.QCD.Acre
#print axioms YM.QCD.Acre.Rails.Reference.Sharp.Price.fitting
#print axioms YM.QCD.Acre.Rails.Reference.Sharp.Price.haloPos
#print axioms YM.QCD.Acre.Rails.Reference.Sharp.Price.procMeter
