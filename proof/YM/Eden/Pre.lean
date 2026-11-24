import YM.Eden.Castle
/-! # Envelope with endpoint Book. single-site any horizon.B -/
set_option autoImplicit false
noncomputable section
namespace YM.Massive.Evo
open Function Lattice Wilson RG Metric Precision Bloch Laurent Tensor Work.F03 Exterior
open Finset Filter Matrix AnalyticBridge.LocalGaussianLaws.Current
open YM.Next.Free YM.Bloom YM.Arise YM.Arise.Range Bloom.TreeP
open scoped Topology BigOperators InnerProductSpace Matrix Matrix.Norms.L2Operator TensorProduct Classical
variable {G:Gauge}{d k i m j l w r r₀ g q N:ℕ}{c f n:Side} {H:Bed}{t:Clip}{a b:ℝ}{I J :Type}[Fintype I][Fintype J]
open Massive UV QCD QCD.Eden QCD.Grass QCD.Cove Lat Poised.Display
open Elm Elm.SparK Elm.SparK.Arbor Elm.SparK.Arbor.Gallery Elm.SparK.Arbor.PrismD Poised Papyrus Lining
open Poised.Plans RP YM.Source YM.Source.Drops QCD.Anomaly QCD.Creek YM.Eden Girdle Sieve Counting Counting.Terrain Pipes Facets Orientation MassiveQCD.Plate Carte.Hem Permit Civic
-- powers.Light Ore: a scaling subset. kernel Dir.Auth.
variable {P:UV.Label d}{Q:SourceRead.TaperHol}{K:Hol su}{V: Lining.Temper.Collage.Exhibit K}{hk:Drops.Peg K (d/2)}(hp:P.val∈ Rtg d i g q)
local notation "pϱ"=>Gallery.polarity q
lemma moodK {x:UV.Pol d} (h:x∈ Rtg d i g q): moored x pϱ:=by
     refine Submodule.span_induction (p:=fun x _=> moored x pϱ) ?_ (by unfold moored; rw [map_zero,smul_zero]) (fun x y _ _ h hp=>by unfold moored; rw [map_add,h,hp,smul_add]) (fun t x _ h=>by unfold moored; rw [map_smul,h,smul_comm]) h
     rintro _ ⟨p,⟨rfl,rfl,rfl⟩,rfl⟩; unfold moored parityAct UV.gen; rw [TensorProduct.map_tmul]; change _⊗ₜ[ℂ]Grass.grade (mono p.2)=_; rw [Grass.grade_mono, TensorProduct.tmul_smul]; congr 1; unfold Gallery.polarity gammaQ; split; next h=>exact (of_decide_eq_true h : Odd _).neg_one_pow
     next h=> exact (Nat.not_odd_iff_even.mp (of_decide_eq_false (Bool.eq_false_iff.mpr h))).neg_one_pow
lemma red_cap(x: Drape)(hX:Profile x)(y:Mini d)(G:SourceRead.TaperHol)(he: TravelsP G x y):∃ P:Label d,P.val=y.val:=by
    obtain ⟨M,hM⟩:= he; let n:Side:=⟨M+1,Nat.succ_pos _⟩; have h:=hM n 0 (by change M≤M+1; omega); let F:=x n 0; have haz:(∀ k, colorAct k y.val=y.val):=by
         intro k; have hp :=Beacon.coloredO G 0 k _ _ h; have hz:(fun V:Grid n=> slots 6 (fun _=>k) (F (Lattice.gauge (fun _=>k) V)))= ⇑F:= congr_arg DFunLike.coe (hX n 0 (fun _=>k)); apply Beacon.chooses G 0 (Poised.Display.radiant_cap k y.property) y.property _ h; exact hz ▸ hp

    exact ⟨⟨y.val,(label_law _).2 ⟨y.property,haz⟩⟩,rfl⟩
variable (P)
structure ArcP (Y: Drape)(q:Bool)(X:Label d)(V: Lining.Temper.Collage.Exhibit K) (Q:SourceRead.TaperHol)(O:BudgetPoint) (θ α t z:ℝ)(r κ j N:ℕ)(ε:ℝ):Prop where
   swung :∃ x:Label d, ‖prism O.threshold θ d (passport d x)-(passport d X : Mini d)‖ < ε ∧ (∀ (n:Side)(o:Cover),N≤ n.val→Beacon.ActionTest Q o (Y n o) x.val) ∧ (∀ (R:Side)(b:Cover)(H T τ Z:ℝ),1≤ θ → 0≤ H → 0 ≤ T → N≤ R.val → (∀ v:Label d,∀ U:Grid R, load (fun _=>θ) (graphs d V b v U) ≤ H * wealth v.val O.threshold θ) → z*Real.exp (4*81)+ 2*H*α* Real.exp (4*81) ≤ Z → Stamp.Volume Q V O b r (Y R b) x κ j q t τ θ α T Z∧ wealth x.val O.threshold θ ≤ α)
omit hp
lemma award (ε:ℝ){Y:Drape}{C Z:ℝ}{Pc:BudgetPoint}{t v α β:ℝ}{q:Bool}(hY:Profile Y)(hq:∀ n b,Gallery.moon q (Y n b))(ha:0≤ t)(hold:ProofB Q Y (passport d P) Pc v m ε) (hK:Stamp.Pilot Q V d k w l j r₀ α β)(hc:1 ≤C)(hk:Pc.order=k)(hp:Pc.power=w)(hw:max r r₀+1 ≤ Pc.B)(h:∀ c:Side,∀ b:Cover,2*(r+1)<c.val → Priced (Y c b) Pc b r l j v C Z):
    let A:= α*C; ArcP Y q P V Q Pc v (max A ((C+β*A)*Real.exp (81*t))) t Z r₀ l j (m+30*(max r r₀+1)) ε :=by
       intro A; obtain ⟨y,hy,hW⟩:=hold.sells; obtain ⟨p,hp'⟩:=red_cap Y hY y Q ⟨m,hy⟩; rw [show y= passport d p from Subtype.ext hp'.symm] at hW; let Y' := m+30*(max r r₀+1); refine ⟨p,hW,fun n v hn=> hp'.symm ▸ hy n v (le_trans (Nat.le_add_right ..) hn),fun n b H T τ Z' hv hH hT hn hU hz=>?_⟩
       have hk':2*(r+1)<n.val:=by omega -- let Y' assumption hn not Y'
       have he:Beacon.ActionTest Q b (Y n b) p.val:=hp'.symm ▸ hy _ _ ((Nat.le_add_right ..).trans hn); let B:= wealth p.val Pc.threshold v; have hX:= h n b hk'; have hf:B≤A:=hK.earn _ _ _ _ _ _ _ _ hk hp (zero_lt_one.trans_le hv) hX.Fl he; let F:= max A ((C+β*A)*Real.exp (81*t)); have hh:B≤ F:=hf.trans (le_max_left ..);
       refine ⟨?_,hh⟩; apply Stamp.gain Q V b p _ v _ _ Pc _ hK hk hp (max r r₀) (r+1) (le_max_right ..) (Nat.add_le_add_right (le_max_left ..) _) hw (by omega) ha hv he (hY n b) (hq n b) hX.Fl hX.pay hU hH hT
       · apply le_trans _ (le_max_right ..); gcongr; · exact zero_le_one.trans hK.funds
       apply le_trans _ hz; rw[add_mul]; rw [← mul_assoc 2]; gcongr
variable {p:Bard d}
end YM.Massive.Evo
#print axioms YM.Massive.Evo.award
