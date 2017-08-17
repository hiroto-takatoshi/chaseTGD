#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <utility>
#include <iterator>
#include <cassert>
#include <type_traits>
#include <algorithm>

using namespace std;

enum cellType { VAR, CONST, NONE };

struct Cell {
    enum cellType t;
    string v;
    Cell():t(NONE){}
    Cell(enum cellType t_,string v_):t(t_),v(v_){}
    bool isEmpty() { return t==NONE; }
    bool isVar() { return t==VAR; }
    bool isCon() { return t==CONST; }
    bool mapsTo(Cell &c) {
        if(isCon()) {
            return equalTo(c);
        }
        else {
            if(c.isCon()) return true;
            else return equalTo(c);
        }
    }
    bool equalTo(Cell &c) {
        if(t==NONE || c.t==NONE) return true;
        return t==c.t && v==c.v;
    }
    void operator = (const Cell &c) {
        t = c.t;
        v = c.v;
    }
    void show () {
        cout<<v<<" ";
    }
};

struct Atom {
    string name;
    vector<string> attr;

    Atom(){}
    Atom(string n_,vector<string>a_):name(n_),attr(a_){}
};

typedef vector<Atom> Term;

struct TGD {
    Term lhs, rhs;
    vector<string> joinAttr, refAttr, skolemAttr;
    map<string, vector<string> > lFather, rFather;
    map<pair<string,string>, int> lPos, rPos;
    
    TGD(){}
    TGD(Term l,Term r):lhs(l),rhs(r){
        for(auto it : lhs) {
            int len = it.attr.size();
            for(int i = 0; i < len; ++i) {
                string jt = it.attr[i];
                lFather[jt].push_back(it.name);
                lPos[make_pair(it.name, jt)] = i;
            }
        }
        for(auto it : rhs) {
            int len = it.attr.size();
            for(int i = 0; i < len; ++i) {
                string jt = it.attr[i];
                rFather[jt].push_back(it.name);
                rPos[make_pair(it.name, jt)] = i;
            }
        }
        for(auto const &it : lFather)
            if(it.second.size() > 1)
                joinAttr.push_back(it.first);
        for(auto const &it : rFather)        
            if(lFather.count(it.first) > 0)
                refAttr.push_back(it.first);
            else
                skolemAttr.push_back(it.first);
    }
    TGD inverse() {
        return TGD(rhs, lhs);
    }
    bool valid() {
        return !lhs.empty() && !rhs.empty();
    }
};

struct Tuple {
    string name;
    vector<Cell> cs;

    Tuple(){}
    Tuple(string n_,vector<Cell>cs_):name(n_),cs(cs_){}
    
    Tuple(string n_,int x):name(n_) {
        for(int i = 0; i < x; ++i) cs.push_back(Cell());
    }

    bool isPlaceHolder () {
        bool ret = false;
        for (auto i : cs)
            ret |= i.isEmpty();
        return ret;
    }

    bool operator == (Tuple & t) {
        bool ret = (name == t.name) && (t.cs.size() == cs.size());
        for(int i = 0, l = cs.size(); ret && i < l; ++i)
            ret &= (cs[i].equalTo(t.cs[i]));
        return ret;
    }

    void show () {
        cout << name << ":";
        for (auto i : cs) i.show();
        cout << endl;
    }



};

typedef vector<Tuple> Tuples;

struct Peers {
    Tuples staged, localI, localD;
};

typedef Tuples Images;

struct KB { // Knowledge Base
      Peers src, tga;
      Images srci, tgai;
      vector<TGD> tgds, tgdsi;
      int nullCounter;
      void stage() {
          src.staged.clear();
          tga.staged.clear();
          src.staged = srci;
          tga.staged = tgai;
          clearImg();
      }
      void clearImg() {
          srci.clear();
          tgai.clear();
      }
      void clearUnstaged() {
          src.localD.clear();
          src.localI.clear();
          tga.localD.clear();
          tga.localI.clear();
      }
      void init() {
        nullCounter = 0;
        for(auto i : tgds)
            tgdsi.push_back(i.inverse());
      }
};

bool isSubset(Tuples xx, Tuples yy) {
    // x sub of y, for certain sequence on a tgd rhs
    if(xx.size()!=yy.size()) return false;
    int len = xx.size();
    for(int i = 0; i < len; ++i) {
        Tuple x = xx[i], y = yy[i];
        if(x.name!=y.name) return false; // should not happen
        if(x.isPlaceHolder()) continue;
        else if(!x.isPlaceHolder()&&y.isPlaceHolder()) return false;
        else {
            if(!(x==y)) return false;
        }
    }
    return true;
        
}

vector<Tuples> chaseBeta (Images &si, Images &ti, TGD &tgd, Term &term, Term::iterator it, Tuples lt, Tuples rt) {

    // hit; no hit is okay
    // hit once is okay
    // 0 - no hit; 1 - hit; (wrong)
    // return vec of tuples for consistency in skl

    bool ret = false;

    if (it == term.end()) { // check rhs
        // refs on rhs shall be the same

        
        for (auto i : tgd.refAttr) {
            Cell c;
            for (auto j : tgd.rFather[i]) {
                int pos = tgd.rPos[make_pair(j,i)];
                for (auto k : rt) {
                    if (k.name == j) {
                        Cell cc = k.cs[pos];
                        if(c.isEmpty()) {
                            c = cc;
                        }
                        else if (!c.equalTo(cc)) {
                            //cout << "failrefsame" << endl;
                            return vector<Tuples>();
                        }
                    }
                }
            }
        }
        // also skolems
        for (auto i : tgd.skolemAttr) {
            Cell c;
            for (auto j : tgd.rFather[i]) {
                int pos = tgd.rPos[make_pair(j,i)];
                for (auto k : rt) {
                    if (k.name == j) {
                        Cell cc = k.cs[pos];
                        if(c.isEmpty()) {
                            c = cc;
                        }
                        else if (!c.equalTo(cc)) {
                            //cout << "failsklsame" << endl;
                            return vector<Tuples>();
                        }
                    }
                }
            }
        }
        // finally refs shall equal on l&r
        for (auto i : tgd.refAttr) {
            Cell c;
            for (auto j : tgd.rFather[i]) {
                int pos = tgd.rPos[make_pair(j,i)];
                for (auto k : rt) {
                    if (k.name == j) {
                        Cell cc = k.cs[pos];
                        if(c.isEmpty()) {
                            c = cc;
                            goto out1;
                        }
                    }
                }
            }
            out1:
            //cout << "theref" << endl;
            //c.show();
            for (auto j : tgd.lFather[i]) {
                int pos = tgd.lPos[make_pair(j,i)];
                for (auto k : lt) {
                    if (k.name == j) {
                        Cell cc = k.cs[pos];
                        //cout << j << endl << "pos " << pos << endl;
                        //cout << "cc" << endl;
                        //cc.show();
                        if(!c.equalTo(cc)) {
                            //cout << "failrefconsistency" << endl;
                            return vector<Tuples>();
                        }
                        goto out2;
                    }
                }
            }
            out2:;
        }
        // print some hit info
        //cout << "hit" << endl;
        return {rt};
    }
    else { // enum rhs
        vector <Tuples> ret;
        ret.clear();
        for (auto i : ti)
            if((*it).name == i.name) {
                Tuples t_ = rt;
                t_.push_back(i);
                vector<Tuples> vec = chaseBeta(si,ti,tgd,term,next(it),lt,t_);
                if(vec.size()) ret.insert(ret.end(), vec.begin(), vec.end());
            }
        Tuples t_ = rt;
        t_.push_back( Tuple((*it).name,(*it).attr.size()) );
        vector<Tuples> vec = chaseBeta(si,ti,tgd,term,next(it),lt,t_);
        if(vec.size()) ret.insert(ret.end(), vec.begin(), vec.end());
        return ret;
    }
    assert(0);
}

bool chaseAlpha (Images &si, Images &ti, int &np, TGD &tgd, Term &term, Term::iterator it, Tuples now) {
    
    bool done = false;

    //cout << "ALpha" << endl;
    //for (auto i : now) i.show();
    //cout << endl;

    if(it == term.end()) {
        // judge
        bool ok = true;
        for (auto i : tgd.joinAttr) {
            Cell c;
            for (auto j : tgd.lFather[i]) {
                for (auto k : now) {
                    if (k.name == j) {
                        int pos = tgd.lPos[make_pair(j,i)];
                        Cell cc = k.cs[pos];
                        if(c.isEmpty()) {
                            c = cc;
                        }
                        else {
                            if(!c.equalTo(cc)) {
                                ok = false;
                                goto failPoint;
                            }
                        }
                    }
                }
            }
            
        }
        failPoint:;
        if(ok) {
            // return the current vector in stack
            // query & insert, O(n^beta) 
            vector<Tuples> vt = chaseBeta(si,ti,tgd,tgd.rhs,tgd.rhs.begin(),now,Tuples());
            bool cont = true;
            //cout << vt.size() << endl;
            //char ch = getchar();
            do {
                vector<bool> vbool;
                for(vector<Tuples>::iterator it = vt.begin(); it != vt.end(); ++it)
                    vbool.push_back(false);
                cont = false;
                int len = vt.size();
                for(int i = 0; i < len; ++i)
                    for(int j = 0; j < len; ++j)
                        if(j==i || vbool[i] || vbool[j]) continue;
                        else if (isSubset(vt[j], vt[i])) vbool[j]=true;
                vector<Tuples>::iterator it = vt.begin();
                for(int i = 0; i < len; ++i,++it)
                    if(vbool[i]) vt.erase(it);
            } while(cont);
            //cout << vt.size() << endl;
            //ch = getchar();
            
            // if lhs tuples are nothing but nulls, do no insertion
            bool allNull = true;
                for (auto i : now) {
                    for (auto j : i.cs)
                        allNull &= j.isVar();
                }

            // insert a set of fresh labelled nulls to, ti  
            bool added = false;
            for (auto vec : vt) {
                // for every possible rhs pattern

                bool allHit = true;
                for (auto i : vec)
                    allHit &= !i.isPlaceHolder();
                if(allHit) continue;

                Tuples ts_ = Tuples();
                Tuple t;
                for (auto i : vec) {
                    if(i.isPlaceHolder()) {
                        ts_.push_back(Tuple(i.name,i.cs.size()));
                    }
                }
                for (auto i : tgd.skolemAttr) {
                    Cell c;
                    for (auto j : tgd.rFather[i]) {
                        for (auto &k : vec) {
                            if (k.name == j && !k.isPlaceHolder()) {
                                c = k.cs[tgd.rPos[make_pair(j,i)]];
                            }
                        }
                    }
                    if(c.isEmpty()) {
                        int sknum = ++np;
                        c = Cell(VAR, "_" + to_string(sknum));
                    }
                    for (auto j : tgd.rFather[i]) {
                        for (auto &k : ts_) {
                            if (k.name == j) {
                                k.cs[tgd.rPos[make_pair(j,i)]] = c;
                            }
                        }
                    }
                }

                
                for (auto i : tgd.refAttr) {
                    int pos = tgd.lPos[make_pair(tgd.lFather[i][0], i)];
                    Cell c;
                    //cout << "tell me how many times?" << endl;
                    for (auto k : now) {
                        if (k.name == tgd.lFather[i][0]) {
                            
                            c = k.cs[pos];
                            break;
                        }
                    }
                    //cout<<"see1"<<endl,assert(!c.isEmpty()),cout<<"see"<<endl;
                    for (auto j : tgd.rFather[i]) {
                        for (auto &k : ts_) {
                            if (k.name == j) {
                                //cout << "ha?" << endl;
                                k.cs[tgd.rPos[make_pair(j, i)]] = c;
                                //k.show();
                            }
                        }
                        
                    }
                }
                added = true;
                cout << "inserted:" << endl;
                for(auto i : ts_)
                    i.show();
                char ch = getchar();

                ti.insert(ti.end(), ts_.begin(), ts_.end());

            }
            return added;
            
        }
        else {
            // fail added
            return false;
        }
    }
    else {
        // enum, O(n^alpha)
        bool ret = false;
        for(auto i: si) {
            if((*it).name == i.name) {
                Tuples t_ = now;
                t_.push_back(i);
                ret |= chaseAlpha(si,ti,np,tgd,term,next(it),t_);
                //break;
            }
        }
        return ret;
    }
}

bool checkDuplicate (Images &img, Tuple &t) {
    vector <Tuple> :: iterator it = img.begin();
    for(;it!=img.end()&&!(*it==t);++it);
    return it!=img.end();
}   

Images genImage(Peers &base) {
    Images rimg;
    rimg = base.staged;
    for (auto i : base.localI) 
        if (!checkDuplicate(rimg, i))
            rimg.push_back(i);
    for (auto i : base.localD) {
        vector <Tuple> :: iterator it = rimg.begin();
        for(;it!=rimg.end()&&!(*it==i);++it);
        if (it != rimg.end()) {
            // should raise exception
            rimg.erase(it);
        }
    }

    return rimg;
}

int checkViolation(Peers &base, Images &img) {
    // can add more, can't add deleted, can't delete existing
    // true = violate
    // shall raise exception
    Images baseimg = genImage(base);
    for (auto i : img) {
        if(checkDuplicate(base.localD, i)) {
            cout << "violation on local deletion" << endl;
            i.show();
            return 2;
        }
    }
    for (auto i : baseimg) {
        if(!checkDuplicate(img, i)) {
            cout << "violation on local insertion" << endl;
            i.show();
            return 3;
        }
    }
    return 0;
}


int chase(KB &kb) {

    // for every possible firing situation, first do a query, 
    // if no tuples even with labelled nulls satisfy the query, insert a set of fresh nulls.
    // on either direction, it's not ok to delete what's been inserted, vice versa.

    // chase returns 1 for successful propagation, returns 0 for no new modification,
    // returns 2 on invalid insertion and 3 on invalid deletion

    // chase : iterate pattern, query, maybe insert

    bool done (false);
    int err (0);

    //cout << "chase" << endl;

    for(auto t : kb.tgds) {
        // for every TGD
        done |= chaseAlpha(kb.srci,kb.tgai,kb.nullCounter,t,t.lhs,t.lhs.begin(),Tuples());
        if (err = checkViolation(kb.tga, kb.tgai)) {
            cout << "wrong" << endl;
            goto failPoint1;
        }
        else {
            cout << kb.srci.size() << " " << kb.tgai.size() << endl;
            char ch = getchar();

        }
    }

    for(auto t : kb.tgdsi) {
        done |= chaseAlpha(kb.tgai,kb.srci,kb.nullCounter,t,t.lhs,t.lhs.begin(),Tuples());
        if (err = checkViolation(kb.src, kb.srci)) {
            goto failPoint1;
        }
        else {
            cout << kb.srci.size() << " " << kb.tgai.size() << endl;
            char ch = getchar();
        }
    }
    if(!done) return 0;
    return 1; // success

    failPoint1:
    
    return err;

}

void doChaseLoop(KB &kb) {

    // init
    kb.clearImg();
    kb.srci = genImage(kb.src);
    kb.tgai = genImage(kb.tga);

    // while
    int err(0);
    do {
        err = chase(kb);
        if(err > 1) {
            // cout<<"saiyaku"<<endl,assert(0);
            cerr << "end on case of violation" << endl;
            kb.clearImg();
            kb.clearUnstaged();
            return;
        }
        //cout << err << endl;
    } while(err);
    // stage
    kb.stage();
    // show some info
}

KB theKB;

void do0() {

}

void do1() {

}

void do2() {

}

void do3() {

}

void do4() {

}

void do5() {

    

}

void do6() {

    // TODO

}

void do7() {

    exit(0);

}

void showHelp() {
    cout << "-----------------------------------" << endl
         << "| 0. Clean all data.              |" << endl
         << "| 1. Show Constraints.            |" << endl
         << "| 2. Show data (staged and local).|" << endl
         << "| 3. Perform sync.                |" << endl
         << "| 4. Perform local insertion.     |" << endl
         << "| 5. Perform local deletion.      |" << endl
         << "| 6. Perform local merge.         |" << endl               
         // Merge is like del 2 and ins 1
         // (possibly wrong) we are assigning some nulls to others, need to check consistency
         << "| 7. Quit.                        |" << endl
         << "-----------------------------------" << endl;
}

void handle(int o) {
    void (*func[])() = {do0, do1, do2, do3, do4, do5, do6, do7};
    (*func[o])();
    cout<<"donehandle"<<endl;
}

// temp
int main1() {
    // temp definitions here

    KB myKB;
    myKB.tgds = { TGD ( { Atom ( "T" , { "x" , "y" } ) } , { Atom ( "U" , { "x", "y", "z" } ) } ) }; 
    myKB.src.localI = { Tuple ( "T", { Cell(CONST, "1") , Cell(CONST, "2") } ) };

    
/*
    myKB.tgds = {
        TGD ( { Atom ( "U" , { "x" , "y" , "z" } ) } , { Atom ( "T" , { "x" , "y" , "z" } ) } ),
        TGD ( { Atom ( "R" , { "x" , "y" } ) , Atom ( "S" , { "x" , "z" , "w" } ) } , { Atom ( "T" , { "x", "y", "z" } ) , Atom ( "V" , { "w", "x" } ) } )
    };

    myKB.src.localI = {
        Tuple ( "R", { Cell(CONST, "1") , Cell(CONST, "1") } ),
        Tuple ( "R", { Cell(CONST, "3") , Cell(CONST, "2") } ),
        Tuple ( "S", { Cell(CONST, "1") , Cell(CONST, "1") , Cell(CONST, "4") } ),
        Tuple ( "S", { Cell(CONST, "1") , Cell(CONST, "2") , Cell(CONST, "4") } ),
        Tuple ( "U", { Cell(CONST, "3") , Cell(CONST, "2") , Cell(CONST, "3") } )

    };

    myKB.tga.localI = {
        
        Tuple ( "V", { Cell(CONST, "5") , Cell(CONST, "3") } )

    };
    
    myKB.tga.localD = {
        
        Tuple ( "T", { Cell(CONST, "3") , Cell(CONST, "2") , Cell(CONST, "3") } ),
        Tuple ( "T", { Cell(CONST, "1") , Cell(CONST, "1") , Cell(CONST, "1") } )
    };
    
*/
    myKB.init();

    doChaseLoop(myKB);

    exit(0);
}

int main() {
    main1();
    
    while(true) {
        showHelp();
        int o;
        cin >> o;
        if(cin.fail()) showHelp();
        if(!o) return 0;
        if(o > 0 && o < 8) handle(o);
        //else showHelp();
    }
    return 0;
}
