import YM.Mural.Sym
import YM.QCD.Villa.Music
import YM.Mural.Flora
set_option maxHeartbeats 1500000
set_option maxRecDepth 2400
/-! # Linear plate laws at Gauge transfer. -/
set_option autoImplicit false
noncomputable section
namespace YM.MassiveQCD.PaletteT
open QCD QCD.Grass QCD.Creek QCD.Sway QCD.Sway.OrbitG Function Finset Filter MeasureTheory NormedSpace Cupola QCD.Cove QCD.Cove.Send QCD.Lat
open Plate Stitch Tablet Ribbon Lattice Wilson RG
open scoped BigOperators Topology Classical ContDiff Matrix
variable {A B I J E L:Type}[Fintype A][Fintype B][Fintype I]
variable {N:ℕ}{c f:Side} {R:Ratio c f} {P:Rise f N E J}
local notation "Ip" => Option I
local notation "Sp" => Spine Unit
local notation "Xp" => Keys f N ⊕ Spine Unit
variable {o:Unit→Site f}{q:Unit→Bool}
lemma giftE {p: Option I→ Patio (A⊕ Spine Unit)} (h:Polite q ∅ (p none))(hy:∀ i,ValidPieces A q univ (p i))(hh: ∀ i,vacR Sp A (p i)=vacR Sp A (p none)): Loose q p:=⟨h,hy,hh⟩
lemma tur (D:A→ ℂ)(y:Option I→ Patio (A⊕ Spine Unit)) {T:Finset Unit} (hx:y none=0 ∨ T=∅)(hy:∀ i,Polite q T (y i))(hp: T=∅ → ∀ i,y i=y none) : Loose q y:=by
    refine ⟨?_,fun i=> ValidPieces.role _ (hy i) (subset_univ _), ?_⟩
    · cases hx with | inl h=> rw [h]; exact polite_nil .. | inr h=> exact h ▸ (hy none)
    intro i; by_cases h:T=∅; rw [hp h i]
    have he i:vacR Sp A (y i)=0:=by apply Subtype.ext; change resetM Sp A _=0; rw [show light _ (y i)=stake A _ _ from (hy i).exact.symm,judgeB]; exact if_neg (burstPos q (nonempty_iff_ne_empty.mpr h)|>.ne_empty)
    rw [he,he]
-- point Jacobian
variable (X: Option I→Tablet P Unit) (r:ℝ) (K:Delta I)(W:Lat.Frame f)
structure Payment (q:Unit→Bool) : Prop where
   title:straight K
   sizeE i U : Loose q (fun j=> (X j).read r U i)
   sizeK i U : Loose q (fun j=> (X j).plug i U)
   paidE j U: Binds K (dance Unit W N) (fun i=> (X i).read r (gauge W U) j) (fun i=> (X i).read r U j)
   paidK j U: Binds K (dance Unit W N) (fun i=> (X i).plug j (gauge W U)) (fun i=> (X i).plug j U)
variable (Q:Send R N L) (s: Finset (Fj L E J)) (he: Payment X r K W q)
include he
open Fj
lemma tinted (u: Grid f): Binds K (dance Unit W N) (fun i=> (X i).made r (gauge W u) s) (fun i=> (X i).made r u s) ∧ Loose q (fun i=> (X i).made r u s):=by
    let A:= graph (P:=I) q (Keys f N); let P i (j:E):= NormedSpace.exp ((X i).read r u j)-1; let E0:= leftE s; let L0:=spent s; let C i := ∏ j∈E0,P i j; let F i:= ∏ j∈L0,(X i).plug j u; let w:= dance Unit W N
    have hu : (fun _: Ip=> (1:Patio Xp))∈A:= Loose.oneV I (Keys f N) q
    have hv :straight K:=he.title
    have hA(x)(h:x∈ A)(y)(g:y∈ A) : x*y ∈ A:= Loose.light (show Loose _ _ from h) g
    have hO(x)(h:x∈ A)(y)(g:y∈ A)(i j):(x i-x none)*(y j-y none)=0:=fare (show Loose _ _ from h) g i j
    have hp (j:E): (fun i=> P i j)∈A:=by
        have hz: (fun j' => exp ((X j').read r u j)) ∈ A:= live_pow _ _ (he.sizeE j u); exact A.sub_mem hz hu

    have hz(i:E): Binds K w (fun j=> exp ((X j).read r (gauge W u) i)-1) (fun j=> P j i):= by
        let x i' := exp ((X i').read r (gauge W u) i); let y i':= exp ((X i').read r u i)
        let F:=alphabet K w
        have hv1 : (((fun _:Option I=>(1:Patio Xp)),(fun _:Option I=>(1:Patio Xp)))) ∈ F:= unity K w hv _ _ (map_one _)
        have hg: (x,y)∈ F:=binds_exp K w A hu hA hO (he.paidE i u) hv (he.sizeE i u)
        have hq:= F.sub_mem hg hv1; exact show Binds K w (x-1) (y-1) from hq

    have hf (i:J) : (fun j=> (X j).plug i u)∈ A:= he.sizeK i u
    have hV:Binds K w (fun i=> ∏ j∈E0,(exp ((X i).read r (gauge W u) j)-1)) C:=binds_prod K w A hu hA hO (fun e i=> exp ((X i).read r (gauge W u) e)-1) (fun e i=>P i e) E0 (fun i _=> hp i) (fun i _=> hz _) hv -- parentheses sum minus syntax
    have h1 {Z:Type} (s:Finset Z)(f:Ip→ Z→ Patio Xp) (hh:∀ i,(fun j=> f j i)∈A): (fun i=>∏ j∈s,f i j)∈A:=by
        induction s using Finset.induction_on with
        | empty=>simp only [prod_empty]; exact hu
        | insert i s hi ih=> simp only [prod_insert hi]; exact hA _ (hh i) _ ih
    have hQ: Binds K w (fun i=>∏ j∈L0,(X i).plug j (gauge W u)) F:= binds_prod K w A hu hA hO (fun j i=>(X i).plug j (gauge W u)) (fun j i=> (X i).plug j u) L0 (fun i _=> hf i) (fun i _=>he.paidK i u) hv
    have hC:=h1 E0 P hp; have hf:= h1 L0 (fun i j=>(X i).plug j u) hf; have hy: Loose q (C*F):= hA C hC F hf
    rw [show (fun i=>(X i).made r u s)=C*F from rfl]
    exact ⟨binds_mul K w hv hV hQ (hO C hC F hf),hy⟩
-- transport
variable (U:Grid f){Q}
omit he
noncomputable def rift (Q: Send R N L) (U:Grid f)(s:Finset (Fj L E J)) : Patio Xp→L[ℂ] Patio (Keys c N ⊕ Spine Unit) := LinearMap.toContinuousLinearMap ((((carry Sp (Tablet.tunnel Q s U)).comp ((Cove.light _).toLinearMap.toContinuousLinearMap)).toLinearMap).codRestrict ((roomA (Keys c N⊕Spine Unit)).toSubmodule) (fun x=>evenCarry Sp _ (tunnelP (P:=P) Q _ _ ) _ (bright x))) -- P implicit maybe not resolvable
lemma banksQ (x:Patio Xp) (hh : ValidPieces (Keys f N) q univ x) : ValidPieces (Keys c N) q univ (rift (P:=P) Q U s x) :=by
    rw [hh.wholeV,map_sum]; refine ValidPieces.cost _ _ (fun i _=>ValidPieces.role i (politeStep _ (choseTuft _ _ _ _) rfl) (subset_univ _))
lemma quietQ {f:Option I→Patio Xp}(h: Loose q f) : Loose q (fun i=>rift (P:=P) Q U s (f i)):=by
    refine ⟨politeStep _ h.plain rfl,fun i=> banksQ s U _ (h.finance i),fun i=>?_⟩ -- args
    apply Subtype.ext; change resetM Sp _ (carry _ _ _)= resetM Sp _ (carry _ _ _); rw [revive,revive,wing,wing,←revive,← revive]; exact congr_arg _ (congr_arg Subtype.val (h.bonds i))
lemma danceV {c:Side} (p:Lat.Frame c)(x: Tine c N Unit): (dance Unit p N x).val=carry Sp (Lat.slots N p).toLinearMap.toContinuousLinearMap x.val:=rfl
lemma raft (x:Tine f N Unit): (rift (P:=P) Q U s x).val=carry Sp (Tablet.tunnel Q s U) x.val:=rfl
lemma turnCap [Countable E] [Countable J] (h:Toned Q) (x:Patio Xp):
    dance Unit (W∘ R.embed) N (rift (P:=P) Q (gauge W U) s x)= rift (P:=P) Q U s (dance Unit W N x):=by
     apply Subtype.ext; show ((dance Unit _ N) (rift (P:=P) Q (gauge W U) s x)).val=(rift (P:=P) Q U s (dance Unit W N x)).val; simp_rw [danceV,raft,danceV]; apply vista (Keys c N); intro i; rw [wing,wing,wing,wing]; exact drivesAtG Q U W h s _
lemma rotation_print (v:Tablet P Unit): v.dye r Q s U=rift (P:=P) Q U s (v.made r U s):=by
     apply Subtype.ext; exact rfl
include he
lemma horizon [Countable E] [Countable J] (hp:Toned Q): Binds K (dance Unit (W∘ R.embed) N) (fun i=>(X i).hue r Q s (gauge W U)) (fun i=> (X i).hue r Q s U)∧ Loose q (fun i=>(X i).hue r Q s U):=by
    unfold Tablet.hue Cove.closeS; rw [gauge_flags]; split; swap; · exact ⟨unity _ _ he.title 0 0 (map_zero _), (graph (P:=I) q (Keys c N)).zero_mem⟩
    obtain ⟨h,hQ⟩:=tinted X r K W s he U
    simp_rw [rotation_print r] -- X arg?
    refine ⟨fun i=>?_, quietQ s U (P:=P) (Q:=Q) hQ⟩
    change (dance Unit (W ∘ R.embed) N) (rift (P:=P) Q (gauge W U) s ((X i).made r (gauge W U) s))=aggregate (fun j=> K i j) (fun i=>rift (P:=P) Q U s ((X i).made r U s)); rw [turnCap W s U hp, h i]; unfold aggregate; rw [map_sum]; exact sum_congr rfl fun _ _=>map_smul ..
end YM.MassiveQCD.PaletteT
#print axioms YM.MassiveQCD.PaletteT.horizon
