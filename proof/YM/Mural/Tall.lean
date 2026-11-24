import YM.Mural.Chisel
import YM.MassiveQCD.Cupola.Dollar
import YM.MassiveQCD.Stitch.Mint
import YM.MassiveQCD.Plate.Lotion
/-! # Assertions on encodings. Counted only physical letters. -/
set_option autoImplicit false
noncomputable section
namespace YM.QCD.Mural
open Cove Send Lat Kit Lattice Wilson Finset Function Grass Creek Filter NormedSpace RG Loom
open scoped BigOperators Topology ContDiff Classical Matrix
open MassiveQCD.Ribbon MassiveQCD.Stitch MassiveQCD.Cupola MassiveQCD.Apron
variable {I R A:Type}[Fintype I][Fintype R][Fintype A] {N:ℕ}{c f:Side}
variable (N:ℕ)(I:Type)[Fintype I]
variable (c) (p:I→Site c)(t b:ℝ)(n:ℕ)
local notation "M"=> ample N I
local notation "X"=> Keys c N ⊕ Spine I
local notation "A"=> Keys c N
local notation "U"=> Keys c M
local notation "Y"=> Spine I
noncomputable abbrev family : Finset U := univ.map (shapeE N I c)
noncomputable def leftKeys (K R:Type)[Fintype K][Fintype R] : Finset (K⊕R):= Finset.disjSum univ ∅
lemma counted : family c N I= (leftKeys A Y).map (territory N p):=by
    ext i; constructor
    · intro h; obtain ⟨a,ha,rfl⟩:=mem_map.mp h; exact mem_map.mpr ⟨Sum.inl a,inl_mem_disjSum.mpr ha,rfl⟩
    intro h; obtain ⟨a,ha,rfl⟩:=mem_map.mp h; unfold leftKeys at ha; rcases a with a|a; exact mem_map.mpr ⟨a,inl_mem_disjSum.mp ha,rfl⟩; simp at ha
noncomputable abbrev premiumE (x:Patio X):= repay (leftKeys A Y) b n (Tablet.chip t A Y) (light _ x)
noncomputable abbrev premiumG (x:EvenA c M):= repay (family c N I) b n (fun _=> t) (light _ x)
lemma penKey (x:Alg X) : surge (family c N I) b n (pen N p t x)= pen N p t (surge (leftKeys A Y) b n x):=by
    rw [←write x]; simp_rw [map_sum,map_smul]; apply sum_congr rfl; intro i _; rw [boomM]; apply congr_arg ((coef i x) • ·)
    rw [pen,AlgHom.comp_apply,AlgHom.comp_apply,map_smul,map_smul]; let E:=territory N p; let w:X→ℝ:=Sum.elim (fun _=>1) (fun _=>t⁻¹)
    have hv: stretch t⁻¹ A Y (mono i)=((∏ j∈i,(w j:ℂ))) • mono i:=by
       apply Eq.trans _ (wscale_mono w i); refine congr_arg (fun M':Matrix X X ℂ=>changeVars M' (mono i)) ?_; congr! 1; funext i
       rcases i with i|i; exact Complex.ofReal_one.symm; simpa [w]
    have hp:premium (family c N I) b n (i.map E)=premium (leftKeys A Y) b n i:=by rw [premium,premium,counted c N I p,← Finset.map_inter,card_map]; congr! 8
    rw [hv,map_smul,map_smul]; obtain he|he:=embed_blade E i <;> change embed E (mono i)=_ at he
    · change _ • surge _ _ _ (embed E (mono i))= _ • (_ • embed E (mono i)); rw [he,boomM,hp]; rw [smul_comm]
    change _ • surge _ _ _ (embed E (mono i))= _ • (_ • embed E (mono i)); rw [he,map_neg,boomM,hp]; rw [smul_neg,smul_neg,smul_neg, smul_comm]
lemma stake_key (z:Finset R)(i: Alg A): surge (leftKeys A R) b n (stake A z i) = stake _ z (surge (univ:Finset A) b n i):=by -- A shadow
    rw [←write i,map_sum,map_sum,map_sum,map_sum]; refine sum_congr rfl fun j _=>?_ ; simp_rw [map_smul,boomM (univ:Finset A)]; rw [map_smul]; have h:premium (leftKeys A R) b n (j.disjSum z) =premium (univ:Finset A) b n j:=by
       have hx:(j.disjSum z)∩ leftKeys A R=j.disjSum ∅:=by ext x; rcases x with x|x <;> simp [leftKeys]
       have hh: b ^ (min n ((j.disjSum z) ∩ leftKeys A R).card)=b^ (min n (j∩univ).card):=by rw [hx,card_disjSum,Finset.card_empty,Nat.add_zero,inter_univ]
       unfold premium; convert! hh
    obtain hv|hv:=broken j z; · rw [hv,boomM,h]
    rw [hv,map_neg,boomM,h,smul_neg,smul_neg,smul_neg]
variable {q:I→Bool}{S:Finset I}
lemma attachedM (h:0<t)(x:Tine c N I)(hx:Polite q S x): premiumE c N I t b n x=repay univ b n (fun _:Keys c N=> t) (scrape A (burst q S) x.val):=by
    let z:=burst q S; let p:= scrape A z x.val; change load _ (surge _ b n x.val)=_
    change load (expRate (p:=fun _: A =>t) (q:=fun _:Y=>1)) (surge (leftKeys A Y) b n x.val)=load (fun _:A=>t) (surge univ b n p)
    conv_lhs => rw [show x.val=stake _ z p from hx.exact.symm,stake_key, stakesBill (p:=fun _=>t) (q:=fun _=>1) (fun _=>h) (fun _=>one_pos)]
    simp
lemma pennedM (h:0<t)(x:Tine c N I)(hx:Polite q S x): premiumG c N I t b n (banknote N p t x)= premiumE c N I t b n x:=by
    rw [attachedM c N I t b n h x hx]; unfold premiumG repay; rw [bank_spent,penKey]; let z:=burst q S; let v:=scrape A z x.val
    rw [show light _ x= stake _ z v from hx.exact.symm,stake_key]; exact penkin N p t _ h _ -- syntax
lemma mintAlt (s:Finset I)(h:0<t)(x:EvenA c M)(hp: Mint N p t q s x): premiumE c N I t b n (withdraw N p t x)=premiumG c N I t b n x:= (pennedM c N I p t b n h _ hp.shows).symm.trans (congr_arg _ hp.spark)
end YM.QCD.Mural
#print axioms YM.QCD.Mural.mintAlt
