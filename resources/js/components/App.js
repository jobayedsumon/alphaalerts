import React, {Component, Suspense, useEffect} from 'react'
import { HashRouter, Route, Routes } from 'react-router-dom'
import './scss/style.scss'
import fetchWrapper from "./helpers/fetchWrapper";
import {useDispatch, useSelector} from "react-redux";
import {logout} from "./helpers/authHelper";

const loading = (
  <div className="pt-3 text-center">
    <div className="sk-spinner sk-spinner-pulse"></div>
  </div>
)

// Containers
const DefaultLayout = React.lazy(() => import('./layout/DefaultLayout'))

// Pages
const Login = React.lazy(() => import('./views/pages/login/Login'))
const Register = React.lazy(() => import('./views/pages/register/Register'))
const Page404 = React.lazy(() => import('./views/pages/page404/Page404'))
const Page500 = React.lazy(() => import('./views/pages/page500/Page500'))


const App = () => {
    const dispatch = useDispatch();
    const token = useSelector(state => state.token);

    const checkToken = () => {
        if (token) {
            fetchWrapper.defaults.headers.common['Authorization'] = 'Bearer ' + token;
        } else {
            dispatch({type: 'set', user: null, token: null});
            logout();
        }
    }

    useEffect(() => {
        checkToken();
        fetchWrapper.interceptors.response.use(
            response => response,
            error => {
                if (error.response.status === 401) {
                    checkToken();
                }
                return Promise.reject(error);
            }
        );
    }, [token]);

    return (
      <HashRouter>
        <Suspense fallback={loading}>
          <Routes>
            <Route exact path="/login" name="Login Page" element={<Login />} />
            {/*<Route exact path="/register" name="Register Page" element={<Register />} />*/}
            {/*<Route exact path="/404" name="Page 404" element={<Page404 />} />*/}
            {/*<Route exact path="/500" name="Page 500" element={<Page500 />} />*/}
            <Route path="*" name="Home" element={<DefaultLayout />} />
          </Routes>
        </Suspense>
      </HashRouter>
    )
}

export default App
