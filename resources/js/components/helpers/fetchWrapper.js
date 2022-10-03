import axios from "axios";
import {logout} from "./authHelper";

const fetchWrapper = axios.create({
    headers: {
        'Content-Type': 'application/json',
        'Accept': 'application/json',
    },
});

fetchWrapper.interceptors.response.use(
    response => response,
    error => {
        if (error.response.status === 401) {
            logout();
        }
        return Promise.reject(error);
    }
);

export default fetchWrapper;
