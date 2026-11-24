import YM.Arise.Pence
/-! # Ledger caps independent of marker universe. -/
set_option autoImplicit false
noncomputable section
namespace YM.Arise.Parcel
open Function Lattice Finset Wilson Filter MeasureTheory Tensor Work.G06 RG
open scoped Topology InnerProductSpace Matrix.Norms.L2Operator ContDiff BigOperators Classical TensorProduct
open Massive UV UV.Free QCD QCD.Grass QCD.Bera QCD.Cove QCD.Anomaly QCD.Creek Count Vest
open MassiveQCD.Sample.Quills
open MassiveQCD.Ribbon
open YM.Arise.Range YM.Arise.Bill
open MassiveQCD.Play MassiveQCD.Play.Chamber
variable {n m i j d k l:ℕ}
variable {I X Y B A C F D:Type}[Fintype I][Fintype X][Fintype Y][Fintype A][Fintype B][Fintype C][Fintype F][Fintype D]
open MassiveQCD.FlareV
open Next.Rank Normal
variable (q:I→Bool)(w:I→ℕ)
noncomputable def tagE (w:I→ℕ)(i:I):Finset (Svg w):=univ.filter fun a=>a.1=i
noncomputable def occupant (a: Tv w):I:= Sum.elim Sigma.fst (fun v=>v.1.1) a
noncomputable def tagP (w:I→ℕ)(i:I):Finset (Tv w):= univ.filter fun a=>occupant w a=i
local notation "Ec"=>Ledger
local notation "K"=>Arms w
local notation "Ux"=> Tv w
local notation "Sk"=> Spine I
-- site-wise proof.Tensor induction independent of qknips. for GIVEN p:Sigh, same grant. ∀ᶠ params.Elites.Fr.
noncomputable def Coin (a:Bool)(d:ℕ) (p:Cups d a) (n j:ℕ)(C:ℝ): Prop:=∀ (I:Type)[Fintype I](q:I→Bool)(w:I→ℕ)(i:I)(X:Cups (w i) (q i)), w i=d→q i=a→HEq X p→ Bill.port q w i X∈ Ledger (tagP w i) (tagE w i) n j ∧ cents (port q w i X)≤C
variable (i:I)
open MvPolynomial
lemma spin_mem (s:Grace (w i) (q i)) : (house q w i s).val∈ Rim (tagP w i) (Fintype.card (Pairs (SpinMode (w i)))+6):=by
    let L(a:Pairs (SpinMode (w i))):K :=⟨i,a⟩; let f:=embed L; let t:=MassiveQCD.Ribbon.burst q {i}; let g(j:Pairs (SpinMode (w i))):Ux:= Sum.inl (L j); let V:=tagP w i
    change MassiveQCD.Ribbon.stake K t (embed L s.val)∈ _; rw [MassiveQCD.Ribbon.markedOut]; refine Rim.multiply (?_) (?_)
    · rw [← write s.val,map_sum,map_sum]; refine Submodule.sum_mem _ (fun p _=>?_); rw [map_smul,map_smul]; apply Submodule.smul_mem; obtain ⟨j,h1,h2,he⟩:=expression p; rw [he,map_list_prod,map_list_prod,List.map_ofFn,List.map_ofFn]
      have he (l:List (Pairs (SpinMode (w i)))):((l.map g).map atom).prod ∈ Rim (tagP w i) l.length:=by induction l with
        | nil=>rw [List.map_nil,List.map_nil,List.prod_nil]; exact Rim.one _
        | cons a l ih=> rw [List.map_cons,List.map_cons,List.prod_cons,List.length_cons,Nat.add_comm]; exact Rim.multiply (Rim.atoms (U:=tagP w i) (mem_filter.mpr ⟨mem_univ _,show occupant w (g a)=i from rfl⟩)) ih -- args.s
      have hx:= Rim.monotone (Subset.refl _) (show p.card ≤ Fintype.card (Pairs (SpinMode (w i))) from card_le_univ p) (by simpa only [List.length_ofFn,List.map_ofFn] using he (List.ofFn j)) -- clarify
      convert! hx using 1; congr 2; ext z; simp only [Function.comp_apply, fiber, embed_atom]; rfl -- proof edit
    obtain ⟨j,h1,h2,he⟩:= expression t; let f : Sk ↪ Ux:= Embedding.inr; have ht':(t.map f).card ≤ 6:=by unfold t; rw [Finset.card_map,onePost]; split<;> omega
    have hh: t.map f⊆tagP w i :=by intro j hj; obtain ⟨x,hx,rfl⟩:=Finset.mem_map.mp hj; refine mem_filter.mpr ⟨mem_univ _,?_⟩; exact Finset.mem_singleton.mp (located _ _ _ hx)
    have hg:=Rim.layerIn hh ht'
    rcases embed_blade f t with h|h<;> change embed f _∈ _<;>rw [h]; exact hg; exact Submodule.neg_mem _ hg
lemma sparksB (s: Grace (w i) (q i)): ‖house q w i s‖ ≤ ‖s.val‖:=by
   let f: Pairs (SpinMode (w i)) ↪ K:= ⟨fun x=> (⟨i,x⟩:K),(fun a b h=>eq_of_heq (Sigma.mk.inj h).2)⟩; let v:= embed f s.val; let Z:=MassiveQCD.Ribbon.burst q {i}; change ‖MassiveQCD.Ribbon.stake K Z v‖ ≤ _; rw [MassiveQCD.Ribbon.markedOut]; refine (norm_mul_le ..).trans ?_; rw [show ‖fiber Sk v‖=‖s.val‖ from (scenic Embedding.inl v).trans (scenic f s.val),show ‖quill K (mono Z)‖=1 from (scenic (Embedding.inr) (mono Z)).trans (norm_mono Z),mul_one]
lemma spinCapP (s:Finset (Tube su (w i)))(p:Lily su (w i))(h:p∈ Camp s n): nameG w i p∈ Camp (tagE w i) n:=by
    let J(x:Tube su (w i)):Svg w:=⟨i,x⟩; let V:Matrix (Tube su (w i)) (Svg w) ℂ:= Matrix.of fun i j=> if J i=j then 1 else 0
    have hv:nameG w i=Normal.exchange (spool V):=by ext1 x; change MvPolynomial.rename J (MvPolynomial.X (R:=ℂ) x)= Normal.exchange (spool V) (MvPolynomial.X x); rw [wool,MvPolynomial.rename_X]; unfold V; simp [Matrix.of_apply,ite_smul] -- orientation
    rw [hv]; exact horoscope V h (fun a ha k hk=>by by_contra H; exact hk (show V a k=0 from if_neg (fun he:J a=k=> H (he ▸ (mem_filter.mpr ⟨mem_univ _,(show (J a).1=i from rfl)⟩)))))
lemma namesR (s:Finset (Tube su (w i)))(p:Lily su (w i))(h:p∈ Camp s n): cents (nameG w i p) ≤ cents p:=by
    let J(x:Tube su (w i)):Svg w:=⟨i,x⟩; let V:Matrix (Tube su (w i)) (Svg w) ℂ:= Matrix.of fun i j=> if J i=j then 1 else 0
    have hv:nameG w i=Normal.exchange (spool V):=by ext1 x; change MvPolynomial.rename J (MvPolynomial.X (R:=ℂ) x)=Normal.exchange (spool V) _; rw [wool,MvPolynomial.rename_X]; unfold V; simp [Matrix.of_apply,ite_smul]
    rw [hv]; simpa using (gusto V h (show bills V s 1 from fun x _=>by unfold V; simp [Matrix.of_apply,eq_comm, apply_ite Norm.norm]) le_rfl)
lemma fenced {j k:ℕ}{p: Lily su (w i)}(s:Grace (w i) (q i))(hK:p∈ Camp univ j)(he:Fintype.card (Pairs (SpinMode (w i)))+6 ≤ k): port q w i (p⊗ₜ[ℂ]s)∈ Ledger (tagP w i) (tagE w i) j k ∧ cents (port q w i (p⊗ₜ[ℂ]s)) ≤ cents p*‖s.val‖:=by
    rw [portal]; refine ⟨⟨outVault (nameG w i p) (?_),outMask (spinCapP w i _ _ hK) _⟩,(priced (nameG w i p) (house q w i s)).trans ((mul_le_mul (namesR w i _ _ hK) (sparksB q w i s) (norm_nonneg _) (cent p)))⟩; exact Rim.monotone (Subset.refl _) he (spin_mem q w i s)
section
-- Coin flexible.Log budgets both.Val.D
variable {v x y:ℝ}{t: Cups d true}
lemma simpleW {A:Type}[Fintype A](p:MvPolynomial A ℂ): ∃ j,p∈ Camp univ j:=by
    let Kz:=p.support.sup (fun i=>len i); refine ⟨Kz,fun i hp=> ⟨subset_univ _,Finset.le_sup (f:=len) hp⟩⟩
variable {b:Bool}
-- casts T detail using general equalities.We
lemma barter (p:Lily su d)(u:Grace d b)(hp:p∈Camp univ n)(h:Fintype.card (Pairs (SpinMode d))+6≤k): Coin b d (p⊗ₜ[ℂ]u) n k (cents p*‖u.val‖):=by
    intro I bI q w i v hW hQ hV; subst d b; rw [eq_of_heq hV]; exact fenced q w i u hp h
lemma zeroC(d:ℕ)(b:Bool): Coin b d 0 n k 0:= by intro I J q w i v hW hQ hz; subst d b; rw [eq_of_heq hz]; rw [map_zero]; exact ⟨Submodule.zero_mem _,by simp⟩
lemma Coin.mono {s: Cups d b}(h:Coin b d s n k x)(hh:n ≤j)(he:k ≤l)(ht:x ≤y):Coin b d s j l y:=by intro I J q w i v hw hq hz; obtain ⟨ha,hb⟩:= h I q w i v hw hq hz; exact ⟨leaguer ha (Subset.refl _) (Subset.refl _) hh he,hb.trans ht⟩ -- h I implicit instance? need check
lemma Coin.add {s t:Cups d b}(hs:Coin b d s n k x)(he:Coin b d t n k y): Coin b d (s+t) n k (x+y):=by intro I J q w i v hw hq hz; subst d b; rw [eq_of_heq hz]; obtain ⟨h1,h2⟩:=hs I q w i s rfl rfl HEq.rfl; obtain ⟨h3,h4⟩:=he I q w i t rfl rfl HEq.rfl; rw [map_add]; exact ⟨Submodule.add_mem _ h1 h3,le_trans (Bera.wealth ..) (add_le_add h2 h4)⟩
lemma supplies (s:Cups d b):∃ n k:ℕ,∃ v:ℝ, 0 ≤ v ∧ Coin b d s n k v:=by
    induction s using TensorProduct.induction_on with
    | zero=> exact ⟨0,0,0,le_rfl,zeroC d b⟩
    | tmul p u=> obtain ⟨j,h⟩:= simpleW p; exact ⟨j,_,cents p * ‖u.val‖,mul_nonneg (cent _) (norm_nonneg _),barter p u h le_rfl⟩
    | add x y hx hy=>
       obtain ⟨n,k,u,h1,h2⟩:=hx; obtain ⟨m,l,v,h3,h4⟩:=hy; exact ⟨n+m,k+l,u+v,add_nonneg h1 h3,(h2.mono (Nat.le_add_right ..) (Nat.le_add_right ..) le_rfl).add (h4.mono (Nat.le_add_left ..) (Nat.le_add_left ..) le_rfl)⟩
end
end YM.Arise.Parcel
#print axioms YM.Arise.Parcel.supplies
