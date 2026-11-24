import YM.QCD.Finch.Dad
import YM.QCD.Kites.Series
/-! # transport by spice. give height via fareG -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Finch
open Function Lattice Wilson Creek Grass Ledge Lat Kit Finset NormedSpace RG Cove Cove.Send Filter Run
open Sway OrbitG Loom Fleet Bay Strut MeasureTheory Push.Local Push.AbsoluteSums Ursell Gas Graph GasP PhysicalNext.Repeat.Turn Patron Stew Reggae Jets Sun Kites
open scoped BigOperators Topology ContDiff Classical Matrix Matrix.Norms.L2Operator
variable {I J V:Type}{c f:Side}{N n:ℕ}
open Animals
open Flume Orbit Quarry Folding Further.PhysicalPeriodLimitF933 Macrame PhysicalNext.Repeat Deck Meadow
open Pressure ConnectedActivityE6 Blaze King Push.Uniform
open Brick Dust Grove
variable {t s τ u :ℝ}{j k:ℕ}{B:BudgetPoint}
open Stem Kites
variable (G: Gem c N I)(Y:Ruby.Hue c N J){Z K r d b:ℝ}
open Entr Garden Port Footprint AnalyticBridge VerifiedReset Collection
-- reinsertion OR after stencil sym. Crossing ensured. `raw` means CALM.
variable {hf : Grid c→EvenA c N}
lemma roses (Y':Gem c N I)[Fintype I](U:Grid c)(p:Strut c)(hp: Crossing Y'): (∑ i, spice p (Y'.view i (Strut.sky p U))) =∑ i,Y'.view i U:=by
     obtain ⟨e,he⟩:= hp.rays p _ _ (assured p); exact (sum_congr rfl fun i _=> (he i).2 U).trans (Equiv.sum_comp e (fun i=> Y'.view i U))
lemma unSpin (U: Grid c)(h:∀ s:Strut c,spice s (hf (Strut.sky s U))=hf U): potion hf U=hf U:=by
   unfold potion; simp_rw [h,sum_const, ← Nat.cast_smul_eq_nsmul ℝ,card_univ, smul_smul,averageC,inv_mul_cancel₀ (show (Fintype.card (Strut c):ℝ)≠0 from (by positivity)),one_smul]
lemma portray [Fintype I] (M: St c) (hv: Crossing G)(ht:∀ U:Grid c,(∑ i,G.view i U)=paleF N (M U)) (w:ℝ): potion (w • (paleF N∘ M))= w • (paleF N ∘ M):=by
    funext U; apply unSpin U; intro i; simp only [Pi.smul_apply, Function.comp_apply]; rw [eSM _ (phare _),← ht,← ht,map_sum,roses G _ _ hv]
lemma totalsZ [Fintype I](hv:Crossing G)(ht:∀ i,hf i=(∑ j,G.view j i))(i:Grid c):potion hf i=Patron.total G B.threshold i+ Calm.netT (offT G B.threshold) i:=by
    have hp:potion hf i=hf i:=unSpin i (fun s=>by rw [ht,ht,map_sum,roses _ _ s hv]); rw [hp,ht]
    unfold Patron.total Calm.netT; rw [tsum_fintype,tsum_fintype,← sum_add_distrib]; exact sum_congr rfl fun i _=>(add_sub_cancel ..).symm
lemma mergeZ (F:Gem c N V) [Fintype V] (D:ℝ)(U:St c)(f:Grid c→ EvenA c N)(W:ℝ)(hp:Compass G Y B r Z t u d b f)(ht:Crossing F)(hh:AnchorT F B t Z D)(hv:∀ x:Grid c,(∑ i,F.view i x)=paleF N (U x))(hr:0≤u)(hk:u+1+1≤ Z)(hJ:1≤t): Compass (weave G (linen F W)) (Ruby.HJoin Y (offT (linen F W) B.threshold)) B (r+ |W| * D) Z t u (d + payment 1 (4*B.B+2) 0 1 1 (|W| *D) u 0) b (f+ W • (paleF N ∘ U)):=by
   have he:= clock F W ht; have hV:=sizeζ F W hh; have hz:0<t:=zero_lt_one.trans_le hJ; have hq:= starsX _ hV he hz hr hk; have hS :0≤Z:=by linarith
   refine ⟨guardL _ _ hp.costE hV.law, joinsM _ _ hp.costY hq, pilot _ _ hp.wardG he,fun x=>?_⟩
   let J:=linen F W; let K:=offT J B.threshold
   have hV₀ (v:Grid c): (W • (paleF N ∘ U)) v=(∑ i,J.view i v):=by
       change W • paleF N (U v)=_; rw [← hv,smul_sum]; rfl
   rw [crestedX, hp.projects, totalsZ J he hV₀ x (B:=B),show Stem.income (weave G (linen F W)) B.threshold x=Patron.total _ B.threshold x from rfl,woven_sum _ _ _ (permits G hp.costE hz hS x) (permits _ hV.law hz hS x)]
   have hh:Calm.netT (Ruby.HJoin Y K) x=Calm.netT Y x+ Calm.netT K x:= (firmsM Y K _ _ _ (heart _ hp.costY hr hJ x|>.1.hasSum) (heart K hq hr hJ x|>.1.hasSum)).tsum_eq
   change _=Reggae.ocean c N b+(Stem.income G B.threshold x+Patron.total J B.threshold x)+Calm.netT (Ruby.HJoin Y K) x
   rw [hh]; abel
-- Eq.exact Physics. Base 
variable (S:PathData su)(A:Clip)(T:ℕ→Atom su j){η γ α p P Cv:ℝ}
lemma scalarS (i:Strut c)(U:Grid c)(h: S.Bounds A s d b): Stem.income (sax S A B c N α P) B.threshold (Strut.sky i U)= baker c N (tells S A B α P U):=by
   rw [sproutsP _ _ _ h]; apply congr_arg
   unfold Strut.sky tells receipt
   rw [Song.layer_spread,Song.bill_spread _ _ h.width h.three,Song.bill_spread _ _ h.width h.four,Song.bill_spread _ _ h.width h.two]
-- via Stave summon
open PhysicalNext.Repeat.Song
lemma vaultS (U:Grid c)(s':Strut c)(N:ℕ)(h:Extra.Iteration.Charged T s d)(hz:0<s) : baker c N (P* Extra.Iteration.action T (Strut.sky s' U))= baker c N (P* Extra.Iteration.action T U):=by
    rw [← (shuns T (Strut.sky s' U) h hz).tsum_eq,←(shuns T U h hz).tsum_eq]
    let v: Equiv.Perm (Stave (n:=c)):= Equiv.prodCongr (AnalyticBridge.VerifiedReset.Seat.move s'.1 s'.2) (Equiv.refl _)
    let H x:=(codaX T N P c).view x U; refine (tsum_congr (fun i:Stave (n:=c)=>?_) (g:=H∘v)).trans (v.tsum_eq H)
    refine congr_arg (Reggae.ocean c N) ?_
    have he : (v i).1.view U=i.1.view (Strut.sky s' U):= congr_fun (AnalyticBridge.VerifiedReset.Seat.view_move i.1 s'.1 s'.2) U
    unfold tuneAtom; simp only [Pi.smul_apply,he,show (v i).2=i.2 from rfl]
variable (D₁ D₂ D: St c)
-- subtract two.B; path t.* etc.
lemma patchS (X:ℕ→Atom su 2)(p'₀ p' :ℝ)(h: S.Bounds A s d b)(hp:Extra.Iteration.Charged X r t)(hr:0<r)(U: Grid c) (he: potion (Stem.income G B.threshold) U=Stem.income G B.threshold U)(hH: let F:=paleF N∘ (D₁+D₂); potion F U=F U):
   potion (rural G B S A X P α p'₀ p' D D₁ D₂+p' • (paleF N∘ D)) U=(Patron.total G B.threshold U+baker c N (tells S A B α (P+N*p'₀) U)+baker c N (N* Extra.Iteration.action X U))- paleF N ((D₁+D₂) U):=by
       let W : Grid c →EvenA c N:= fun V=> baker c N (N* Extra.Iteration.action X V); let z:=sax S A B c N α (P+N*p'₀); let X' := Stem.income z B.threshold
       let Y':=paleF N∘ (D₁+D₂)
       have ht : rural G B S A X P α p'₀ p' D D₁ D₂+p' • (paleF N∘ D)= (Stem.income G B.threshold+(X'+W))- Y':=by
            funext i; unfold rural Stem.barP; simp only [Pi.add_apply,Pi.smul_apply,Pi.sub_apply,neg_smul,one_smul,Pi.neg_apply,X',z,W,Y', Function.comp_apply,Port.oneC]; abel
       have hx:potion (-Y') U= -paleF N ((D₁+D₂) U):=by
           have hv:potion Y' U=paleF N ((D₁+D₂) U):=hH
           rw [show potion (-Y') U= - potion Y' U from ?_,hv]; unfold potion; simp only [Pi.neg_apply,map_neg,sum_neg_distrib,smul_neg]
       rw [ht,sub_eq_add_neg, crestedX,crestedX,crestedX,he, hx]
       rw [unSpin U (hf:=W) (fun i=> Eq.trans (Reggae.through ..) (vaultS X U i N hp hr)),unSpin U (hf:=X') (fun i=>by unfold X' z; rw [scalarS _ _ i U h,sproutsP S A U h]; exact Reggae.through ..),show X' U=_ from sproutsP S A U h]; unfold Stem.income W; abel
end YM.QCD.Finch
